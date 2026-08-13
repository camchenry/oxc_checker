use std::{
    env,
    error::Error,
    ffi::OsString,
    fs,
    hint::black_box,
    io::{self, Write},
    path::PathBuf,
    process,
    time::{Duration, Instant},
};

use oxc_allocator::Allocator;
use oxc_checker::{benchmark_support, program};
use serde::Serialize;

const USAGE: &str = "\
Usage: profile_checker [OPTIONS] <ROOT>...

Profile the checker against one or more roots and their transitive imports.

Options:
  --iterations <N>       Measured checker passes (default: 20)
  --warmup <N>           Unmeasured checker passes (default: 3)
  --lib-target <TARGET>  Embedded library target, such as es2022 or esnext
  --no-default-lib       Do not load embedded TypeScript libraries
  --json <PATH>          Write the full machine-readable report to PATH
  --pause-before-check   Wait for Enter after setup so a profiler can attach
  -h, --help             Print this help

Build with --release for measurements. Add --features allocation-stats to
include allocation/reallocation counts in addition to arena byte usage.";

#[derive(Debug)]
struct Options {
    roots: Vec<PathBuf>,
    iterations: usize,
    warmup: usize,
    lib_target: Option<String>,
    no_default_lib: bool,
    json_path: Option<PathBuf>,
    pause_before_check: bool,
}

#[derive(Clone, Copy, Serialize)]
struct UsageSnapshot {
    user_cpu_ms: f64,
    system_cpu_ms: f64,
    peak_rss_bytes: u64,
}

#[derive(Clone, Copy)]
struct AllocationSnapshot {
    used_bytes: usize,
    #[cfg(feature = "allocation-stats")]
    allocations: usize,
    #[cfg(feature = "allocation-stats")]
    reallocations: usize,
}

#[derive(Serialize)]
struct PhaseMeasurement {
    wall_ms: f64,
    user_cpu_ms: f64,
    system_cpu_ms: f64,
    cpu_percent: f64,
    arena_bytes_delta: usize,
    allocations_delta: Option<usize>,
    reallocations_delta: Option<usize>,
    peak_rss_bytes: u64,
}

#[derive(Serialize)]
struct IterationMeasurement {
    iteration: usize,
    checked_types: usize,
    #[serde(flatten)]
    measurement: PhaseMeasurement,
}

#[derive(Serialize)]
struct Distribution {
    min: f64,
    mean: f64,
    median: f64,
    p95: f64,
    max: f64,
    stddev: f64,
}

#[derive(Serialize)]
struct Summary {
    wall_ms: Distribution,
    cpu_ms: Distribution,
    cpu_percent: Distribution,
    arena_bytes_delta: Distribution,
}

#[derive(Serialize)]
struct Workload {
    roots: Vec<PathBuf>,
    files: usize,
    source_files: usize,
    library_files: usize,
    source_bytes: usize,
    semantic_nodes: usize,
    checker_queries: usize,
    warmup_iterations: usize,
    measured_iterations: usize,
    default_lib: bool,
    lib_target: Option<String>,
}

#[derive(Serialize)]
struct Report {
    schema_version: u32,
    pid: u32,
    profile: &'static str,
    allocation_counts_enabled: bool,
    workload: Workload,
    build: PhaseMeasurement,
    planning: PhaseMeasurement,
    process_after_measurement: UsageSnapshot,
    summary: Summary,
    iterations: Vec<IterationMeasurement>,
}

fn main() {
    match parse_options(env::args_os().skip(1)) {
        Ok(Some(options)) => {
            if let Err(error) = run(&options) {
                eprintln!("error: {error}");
                process::exit(1);
            }
        }
        Ok(None) => println!("{USAGE}"),
        Err(error) => {
            eprintln!("error: {error}\n\n{USAGE}");
            process::exit(2);
        }
    }
}

fn parse_options(args: impl Iterator<Item = OsString>) -> Result<Option<Options>, String> {
    let mut options = Options {
        roots: Vec::new(),
        iterations: 20,
        warmup: 3,
        lib_target: None,
        no_default_lib: false,
        json_path: None,
        pause_before_check: false,
    };
    let mut args = args.peekable();
    while let Some(argument) = args.next() {
        match argument.to_str() {
            Some("-h" | "--help") => return Ok(None),
            Some("--iterations") => {
                options.iterations = parse_count(&mut args, "--iterations")?;
            }
            Some("--warmup") => options.warmup = parse_count(&mut args, "--warmup")?,
            Some("--lib-target") => {
                options.lib_target = Some(parse_string(&mut args, "--lib-target")?);
            }
            Some("--no-default-lib") => options.no_default_lib = true,
            Some("--json") => options.json_path = Some(parse_path(&mut args, "--json")?),
            Some("--pause-before-check") => options.pause_before_check = true,
            Some(value) if value.starts_with('-') => {
                return Err(format!("unknown option `{value}`"));
            }
            _ => options.roots.push(PathBuf::from(argument)),
        }
    }
    if options.roots.is_empty() {
        return Err("at least one root file is required".to_string());
    }
    if options.iterations == 0 {
        return Err("--iterations must be greater than zero".to_string());
    }
    if options.no_default_lib && options.lib_target.is_some() {
        return Err("--no-default-lib cannot be combined with --lib-target".to_string());
    }
    Ok(Some(options))
}

fn parse_count(args: &mut impl Iterator<Item = OsString>, option: &str) -> Result<usize, String> {
    parse_string(args, option)?
        .parse()
        .map_err(|_| format!("{option} requires a non-negative integer"))
}

fn parse_string(args: &mut impl Iterator<Item = OsString>, option: &str) -> Result<String, String> {
    args.next()
        .ok_or_else(|| format!("{option} requires a value"))?
        .into_string()
        .map_err(|_| format!("{option} requires a UTF-8 value"))
}

fn parse_path(args: &mut impl Iterator<Item = OsString>, option: &str) -> Result<PathBuf, String> {
    args.next()
        .map(PathBuf::from)
        .ok_or_else(|| format!("{option} requires a path"))
}

fn run(options: &Options) -> Result<(), Box<dyn Error>> {
    let allocator = Allocator::default();
    let (store, build) = measure_phase(&allocator, || build_store(&allocator, options))?;
    let (plans, planning) = measure_phase(&allocator, || {
        Ok::<_, io::Error>(benchmark_support::check_plans(&store))
    })?;

    let workload = Workload {
        roots: options.roots.clone(),
        files: store.entries().len(),
        source_files: store
            .entries()
            .iter()
            .filter(|entry| !entry.is_lib())
            .count(),
        library_files: store
            .entries()
            .iter()
            .filter(|entry| entry.is_lib())
            .count(),
        source_bytes: store
            .entries()
            .iter()
            .map(|entry| entry.source_text().len())
            .sum(),
        semantic_nodes: store
            .entries()
            .iter()
            .map(|entry| entry.semantic().nodes().len())
            .sum(),
        checker_queries: plans
            .iter()
            .map(benchmark_support::CheckPlan::query_count)
            .sum(),
        warmup_iterations: options.warmup,
        measured_iterations: options.iterations,
        default_lib: !options.no_default_lib,
        lib_target: options.lib_target.clone(),
    };

    print_workload(&workload, &build, &planning);
    for _ in 0..options.warmup {
        black_box(check_all(&store, &plans));
    }
    if options.pause_before_check {
        eprint!(
            "setup complete; pid={} (press Enter to begin) ",
            process::id()
        );
        io::stderr().flush()?;
        let mut line = String::new();
        io::stdin().read_line(&mut line)?;
    }

    let mut iterations = Vec::with_capacity(options.iterations);
    for iteration in 1..=options.iterations {
        let (checked_types, measurement) = measure_phase(&allocator, || {
            Ok::<_, io::Error>(black_box(check_all(&store, &plans)))
        })?;
        println!(
            "check {iteration:>3}: wall={:>9.3} ms cpu={:>9.3} ms ({:>6.1}%) arena={:>10} B checked={checked_types}",
            measurement.wall_ms,
            measurement.user_cpu_ms + measurement.system_cpu_ms,
            measurement.cpu_percent,
            measurement.arena_bytes_delta,
        );
        iterations.push(IterationMeasurement {
            iteration,
            checked_types,
            measurement,
        });
    }

    let report = Report {
        schema_version: 1,
        pid: process::id(),
        profile: if cfg!(debug_assertions) {
            "debug"
        } else {
            "release"
        },
        allocation_counts_enabled: cfg!(feature = "allocation-stats"),
        workload,
        build,
        planning,
        process_after_measurement: process_usage()?,
        summary: summarize(&iterations),
        iterations,
    };
    print_summary(&report);
    if let Some(path) = &options.json_path {
        let json = serde_json::to_vec_pretty(&report)?;
        fs::write(path, json)?;
        println!("json report: {}", path.display());
    }
    Ok(())
}

fn build_store<'a>(
    allocator: &'a Allocator,
    options: &Options,
) -> Result<program::ProgramStore<'a>, Box<dyn Error>> {
    let mut builder = program::ProgramStoreBuilder::new(allocator, program::FsProgramHost::new());
    if options.no_default_lib {
        builder = builder.without_default_lib();
    } else if let Some(target) = &options.lib_target {
        builder = builder.with_default_lib_target_name(target)?;
    }
    for root in &options.roots {
        builder = builder.add_root_file(root);
    }
    Ok(builder.build()?)
}

fn check_all(store: &program::ProgramStore<'_>, plans: &[benchmark_support::CheckPlan]) -> usize {
    plans
        .iter()
        .map(|plan| benchmark_support::check_program_with_plan(store, plan))
        .sum()
}

fn measure_phase<T, E>(
    allocator: &Allocator,
    operation: impl FnOnce() -> Result<T, E>,
) -> Result<(T, PhaseMeasurement), E>
where
    E: From<io::Error>,
{
    let usage_before = process_usage()?;
    let allocations_before = AllocationSnapshot::capture(allocator);
    let started = Instant::now();
    let value = operation()?;
    let wall = started.elapsed();
    let allocations_after = AllocationSnapshot::capture(allocator);
    let usage_after = process_usage()?;
    Ok((
        value,
        PhaseMeasurement::between(
            wall,
            usage_before,
            usage_after,
            allocations_before,
            allocations_after,
        ),
    ))
}

impl AllocationSnapshot {
    fn capture(allocator: &Allocator) -> Self {
        Self {
            used_bytes: allocator.used_bytes(),
            #[cfg(feature = "allocation-stats")]
            allocations: allocator.get_allocation_stats().0,
            #[cfg(feature = "allocation-stats")]
            reallocations: allocator.get_allocation_stats().1,
        }
    }
}

impl PhaseMeasurement {
    fn between(
        wall: Duration,
        usage_before: UsageSnapshot,
        usage_after: UsageSnapshot,
        allocations_before: AllocationSnapshot,
        allocations_after: AllocationSnapshot,
    ) -> Self {
        let wall_ms = wall.as_secs_f64() * 1_000.0;
        let user_cpu_ms = usage_after.user_cpu_ms - usage_before.user_cpu_ms;
        let system_cpu_ms = usage_after.system_cpu_ms - usage_before.system_cpu_ms;
        let cpu_ms = user_cpu_ms + system_cpu_ms;
        #[cfg(feature = "allocation-stats")]
        let allocations_delta = Some(
            allocations_after
                .allocations
                .saturating_sub(allocations_before.allocations),
        );
        #[cfg(not(feature = "allocation-stats"))]
        let allocations_delta = None;
        #[cfg(feature = "allocation-stats")]
        let reallocations_delta = Some(
            allocations_after
                .reallocations
                .saturating_sub(allocations_before.reallocations),
        );
        #[cfg(not(feature = "allocation-stats"))]
        let reallocations_delta = None;
        Self {
            wall_ms,
            user_cpu_ms,
            system_cpu_ms,
            cpu_percent: if wall_ms > 0.0 {
                cpu_ms / wall_ms * 100.0
            } else {
                0.0
            },
            arena_bytes_delta: allocations_after
                .used_bytes
                .saturating_sub(allocations_before.used_bytes),
            allocations_delta,
            reallocations_delta,
            peak_rss_bytes: usage_after.peak_rss_bytes,
        }
    }
}

#[cfg(unix)]
fn process_usage() -> io::Result<UsageSnapshot> {
    let mut usage = std::mem::MaybeUninit::<libc::rusage>::uninit();
    // SAFETY: getrusage initializes the pointed-to rusage when it returns zero.
    let result = unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: the successful getrusage call above initialized usage.
    let usage = unsafe { usage.assume_init() };
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    let peak_rss_bytes = u64::try_from(usage.ru_maxrss).unwrap_or_default();
    #[cfg(not(any(target_os = "macos", target_os = "ios")))]
    let peak_rss_bytes = u64::try_from(usage.ru_maxrss)
        .unwrap_or_default()
        .saturating_mul(1_024);
    Ok(UsageSnapshot {
        user_cpu_ms: timeval_ms(usage.ru_utime),
        system_cpu_ms: timeval_ms(usage.ru_stime),
        peak_rss_bytes,
    })
}

#[cfg(unix)]
fn timeval_ms(time: libc::timeval) -> f64 {
    time.tv_sec as f64 * 1_000.0 + time.tv_usec as f64 / 1_000.0
}

#[cfg(not(unix))]
fn process_usage() -> io::Result<UsageSnapshot> {
    Ok(UsageSnapshot {
        user_cpu_ms: 0.0,
        system_cpu_ms: 0.0,
        peak_rss_bytes: 0,
    })
}

fn summarize(iterations: &[IterationMeasurement]) -> Summary {
    Summary {
        wall_ms: distribution(iterations.iter().map(|item| item.measurement.wall_ms)),
        cpu_ms: distribution(
            iterations
                .iter()
                .map(|item| item.measurement.user_cpu_ms + item.measurement.system_cpu_ms),
        ),
        cpu_percent: distribution(iterations.iter().map(|item| item.measurement.cpu_percent)),
        arena_bytes_delta: distribution(
            iterations
                .iter()
                .map(|item| item.measurement.arena_bytes_delta as f64),
        ),
    }
}

fn distribution(values: impl Iterator<Item = f64>) -> Distribution {
    let mut values: Vec<_> = values.collect();
    values.sort_by(f64::total_cmp);
    let mean = values.iter().sum::<f64>() / values.len() as f64;
    let variance = values
        .iter()
        .map(|value| (value - mean).powi(2))
        .sum::<f64>()
        / values.len() as f64;
    Distribution {
        min: values[0],
        mean,
        median: percentile(&values, 0.5),
        p95: percentile(&values, 0.95),
        max: values[values.len() - 1],
        stddev: variance.sqrt(),
    }
}

fn percentile(sorted: &[f64], percentile: f64) -> f64 {
    let index = ((sorted.len() - 1) as f64 * percentile).ceil() as usize;
    sorted[index]
}

fn print_workload(workload: &Workload, build: &PhaseMeasurement, planning: &PhaseMeasurement) {
    println!(
        "workload: {} source + {} lib files, {} bytes, {} nodes, {} queries",
        workload.source_files,
        workload.library_files,
        workload.source_bytes,
        workload.semantic_nodes,
        workload.checker_queries,
    );
    println!(
        "build:    wall={:.3} ms cpu={:.3} ms arena={} B peak_rss={} B",
        build.wall_ms,
        build.user_cpu_ms + build.system_cpu_ms,
        build.arena_bytes_delta,
        build.peak_rss_bytes,
    );
    println!(
        "planning: wall={:.3} ms cpu={:.3} ms arena={} B",
        planning.wall_ms,
        planning.user_cpu_ms + planning.system_cpu_ms,
        planning.arena_bytes_delta,
    );
}

fn print_summary(report: &Report) {
    let wall = &report.summary.wall_ms;
    let cpu = &report.summary.cpu_ms;
    let arena = &report.summary.arena_bytes_delta;
    println!("\nsummary ({} measured passes):", report.iterations.len());
    println!(
        "  wall ms: min={:.3} mean={:.3} median={:.3} p95={:.3} max={:.3} stddev={:.3}",
        wall.min, wall.mean, wall.median, wall.p95, wall.max, wall.stddev,
    );
    println!(
        "  cpu ms:  min={:.3} mean={:.3} median={:.3} p95={:.3} max={:.3}",
        cpu.min, cpu.mean, cpu.median, cpu.p95, cpu.max,
    );
    println!(
        "  arena:   min={:.0} mean={:.0} p95={:.0} max={:.0} bytes/pass",
        arena.min, arena.mean, arena.p95, arena.max,
    );
    println!(
        "  process peak RSS: {} bytes",
        report.process_after_measurement.peak_rss_bytes,
    );
}
