use std::{
    alloc::{GlobalAlloc, Layout, System},
    env,
    error::Error,
    ffi::OsString,
    fs,
    hint::black_box,
    io::{self, Write},
    path::PathBuf,
    process,
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

use oxc_allocator::Allocator;
use oxc_checker::{benchmark_support, program};
use serde::Serialize;

struct TrackingAllocator;

struct SystemAllocationCounters {
    allocation_calls: AtomicU64,
    deallocation_calls: AtomicU64,
    reallocation_calls: AtomicU64,
    allocated_bytes: AtomicU64,
    deallocated_bytes: AtomicU64,
    live_bytes: AtomicU64,
    peak_live_bytes: AtomicU64,
}

static SYSTEM_ALLOCATIONS: SystemAllocationCounters = SystemAllocationCounters {
    allocation_calls: AtomicU64::new(0),
    deallocation_calls: AtomicU64::new(0),
    reallocation_calls: AtomicU64::new(0),
    allocated_bytes: AtomicU64::new(0),
    deallocated_bytes: AtomicU64::new(0),
    live_bytes: AtomicU64::new(0),
    peak_live_bytes: AtomicU64::new(0),
};

#[global_allocator]
static GLOBAL_ALLOCATOR: TrackingAllocator = TrackingAllocator;

// SAFETY: Every allocation operation is forwarded to `System` with its original pointer and
// layout. Successful operations perform only atomic bookkeeping and do not allocate recursively.
unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: Forward the allocation request unchanged to the system allocator.
        let pointer = unsafe { System.alloc(layout) };
        if !pointer.is_null() {
            SYSTEM_ALLOCATIONS.record_allocation(layout.size());
        }
        pointer
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: Forward the allocation request unchanged to the system allocator.
        let pointer = unsafe { System.alloc_zeroed(layout) };
        if !pointer.is_null() {
            SYSTEM_ALLOCATIONS.record_allocation(layout.size());
        }
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        SYSTEM_ALLOCATIONS.record_deallocation(layout.size());
        // SAFETY: The pointer and layout are the values supplied by GlobalAlloc's caller.
        unsafe { System.dealloc(pointer, layout) };
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: Forward the reallocation request unchanged to the system allocator.
        let new_pointer = unsafe { System.realloc(pointer, layout, new_size) };
        if !new_pointer.is_null() {
            SYSTEM_ALLOCATIONS.record_reallocation(layout.size(), new_size);
        }
        new_pointer
    }
}

impl SystemAllocationCounters {
    fn record_allocation(&self, bytes: usize) {
        let bytes = bytes as u64;
        self.allocation_calls.fetch_add(1, Ordering::Relaxed);
        self.allocated_bytes.fetch_add(bytes, Ordering::Relaxed);
        let live_bytes = self.live_bytes.fetch_add(bytes, Ordering::Relaxed) + bytes;
        self.peak_live_bytes
            .fetch_max(live_bytes, Ordering::Relaxed);
    }

    fn record_deallocation(&self, bytes: usize) {
        let bytes = bytes as u64;
        self.deallocation_calls.fetch_add(1, Ordering::Relaxed);
        self.deallocated_bytes.fetch_add(bytes, Ordering::Relaxed);
        self.live_bytes.fetch_sub(bytes, Ordering::Relaxed);
    }

    fn record_reallocation(&self, old_bytes: usize, new_bytes: usize) {
        let old_bytes = old_bytes as u64;
        let new_bytes = new_bytes as u64;
        self.reallocation_calls.fetch_add(1, Ordering::Relaxed);
        self.allocated_bytes.fetch_add(new_bytes, Ordering::Relaxed);
        self.deallocated_bytes
            .fetch_add(old_bytes, Ordering::Relaxed);
        let live_bytes = if new_bytes >= old_bytes {
            self.live_bytes
                .fetch_add(new_bytes - old_bytes, Ordering::Relaxed)
                + new_bytes
                - old_bytes
        } else {
            self.live_bytes
                .fetch_sub(old_bytes - new_bytes, Ordering::Relaxed)
                - old_bytes
                + new_bytes
        };
        self.peak_live_bytes
            .fetch_max(live_bytes, Ordering::Relaxed);
    }
}

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

Build with --release for measurements. System allocator counters are always
enabled. Add --features allocation-stats for arena allocation/reallocation counts.";

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
    system: SystemAllocationSnapshot,
    #[cfg(feature = "allocation-stats")]
    allocations: usize,
    #[cfg(feature = "allocation-stats")]
    reallocations: usize,
}

#[derive(Clone, Copy)]
struct SystemAllocationSnapshot {
    allocation_calls: u64,
    deallocation_calls: u64,
    reallocation_calls: u64,
    allocated_bytes: u64,
    deallocated_bytes: u64,
    live_bytes: u64,
    peak_live_bytes: u64,
}

#[derive(Clone, Copy, Serialize)]
struct SystemAllocationMeasurement {
    allocation_calls: u64,
    deallocation_calls: u64,
    reallocation_calls: u64,
    allocated_bytes: u64,
    deallocated_bytes: u64,
    live_bytes_delta: i64,
    peak_live_bytes: u64,
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
    system_allocations: SystemAllocationMeasurement,
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
    system_allocation_calls: Distribution,
    system_allocated_bytes: Distribution,
    system_live_bytes_delta: Distribution,
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
struct TypeKindCount {
    kind: &'static str,
    count: usize,
}

#[derive(Serialize)]
struct CheckerCensus {
    checked_types: usize,
    registered_types: usize,
    arena_bytes: usize,
    allocations: Option<usize>,
    reallocations: Option<usize>,
    system_allocations: SystemAllocationMeasurement,
    type_kinds: Vec<TypeKindCount>,
}

#[derive(Serialize)]
struct Report {
    schema_version: u32,
    pid: u32,
    profile: &'static str,
    arena_allocation_counts_enabled: bool,
    workload: Workload,
    build: PhaseMeasurement,
    planning: PhaseMeasurement,
    checker_census: CheckerCensus,
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

    let checker_census = checker_census(&allocator, &store, &plans);

    print_workload(&workload, &build, &planning);
    print_checker_census(&checker_census);
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
    println!("\nChecks");
    println!(
        "{:>3}  {:>7}  {:>7}  {:>9}  {:>9}  {:>8}  {:>10}",
        "#", "wall ms", "CPU ms", "arena", "system", "allocs", "live"
    );
    for iteration in 1..=options.iterations {
        let (checked_types, measurement) = measure_phase(&allocator, || {
            Ok::<_, io::Error>(black_box(check_all(&store, &plans)))
        })?;
        println!(
            "{iteration:>3}  {:>7.3}  {:>7.3}  {:>9}  {:>9}  {:>8}  {:>10}",
            measurement.wall_ms,
            measurement.user_cpu_ms + measurement.system_cpu_ms,
            format_bytes(measurement.arena_bytes_delta as u64),
            format_bytes(measurement.system_allocations.allocated_bytes),
            format_count(measurement.system_allocations.allocation_calls),
            format_signed_bytes(measurement.system_allocations.live_bytes_delta),
        );
        iterations.push(IterationMeasurement {
            iteration,
            checked_types,
            measurement,
        });
    }

    let report = Report {
        schema_version: 2,
        pid: process::id(),
        profile: if cfg!(debug_assertions) {
            "debug"
        } else {
            "release"
        },
        arena_allocation_counts_enabled: cfg!(feature = "allocation-stats"),
        workload,
        build,
        planning,
        checker_census,
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

fn checker_census(
    allocator: &Allocator,
    store: &program::ProgramStore<'_>,
    plans: &[benchmark_support::CheckPlan],
) -> CheckerCensus {
    let allocations_before = AllocationSnapshot::capture(allocator);
    let mut checked_types = 0;
    let mut registered_types = 0;
    let mut type_kinds = std::collections::BTreeMap::new();
    for plan in plans {
        let stats = benchmark_support::check_program_with_plan_stats(store, plan);
        checked_types += stats.checked_types;
        registered_types += stats.registered_types;
        for (kind, count) in stats.type_kinds {
            *type_kinds.entry(kind).or_default() += count;
        }
    }
    let allocations_after = AllocationSnapshot::capture(allocator);
    #[cfg(feature = "allocation-stats")]
    let allocations = Some(
        allocations_after
            .allocations
            .saturating_sub(allocations_before.allocations),
    );
    #[cfg(not(feature = "allocation-stats"))]
    let allocations = None;
    #[cfg(feature = "allocation-stats")]
    let reallocations = Some(
        allocations_after
            .reallocations
            .saturating_sub(allocations_before.reallocations),
    );
    #[cfg(not(feature = "allocation-stats"))]
    let reallocations = None;
    CheckerCensus {
        checked_types,
        registered_types,
        arena_bytes: allocations_after
            .used_bytes
            .saturating_sub(allocations_before.used_bytes),
        allocations,
        reallocations,
        system_allocations: SystemAllocationMeasurement::between(
            allocations_before.system,
            allocations_after.system,
        ),
        type_kinds: type_kinds
            .into_iter()
            .map(|(kind, count)| TypeKindCount { kind, count })
            .collect(),
    }
}

fn build_store<'a>(
    allocator: &'a Allocator,
    options: &Options,
) -> Result<program::ProgramStore<'a>, Box<dyn Error>> {
    let mut builder = program::ProgramStoreBuilder::new(allocator, program::FsProgramHost::new());
    if options.no_default_lib {
        builder = builder.without_default_lib();
    } else if let Some(target) = &options.lib_target {
        builder = builder.with_standard_library(target.parse::<oxc_checker::LibTarget>()?.into());
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
            system: SystemAllocationSnapshot::capture(),
            #[cfg(feature = "allocation-stats")]
            allocations: allocator.get_allocation_stats().0,
            #[cfg(feature = "allocation-stats")]
            reallocations: allocator.get_allocation_stats().1,
        }
    }
}

impl SystemAllocationSnapshot {
    fn capture() -> Self {
        Self {
            allocation_calls: SYSTEM_ALLOCATIONS.allocation_calls.load(Ordering::Relaxed),
            deallocation_calls: SYSTEM_ALLOCATIONS
                .deallocation_calls
                .load(Ordering::Relaxed),
            reallocation_calls: SYSTEM_ALLOCATIONS
                .reallocation_calls
                .load(Ordering::Relaxed),
            allocated_bytes: SYSTEM_ALLOCATIONS.allocated_bytes.load(Ordering::Relaxed),
            deallocated_bytes: SYSTEM_ALLOCATIONS.deallocated_bytes.load(Ordering::Relaxed),
            live_bytes: SYSTEM_ALLOCATIONS.live_bytes.load(Ordering::Relaxed),
            peak_live_bytes: SYSTEM_ALLOCATIONS.peak_live_bytes.load(Ordering::Relaxed),
        }
    }
}

impl SystemAllocationMeasurement {
    fn between(before: SystemAllocationSnapshot, after: SystemAllocationSnapshot) -> Self {
        Self {
            allocation_calls: after
                .allocation_calls
                .saturating_sub(before.allocation_calls),
            deallocation_calls: after
                .deallocation_calls
                .saturating_sub(before.deallocation_calls),
            reallocation_calls: after
                .reallocation_calls
                .saturating_sub(before.reallocation_calls),
            allocated_bytes: after.allocated_bytes.saturating_sub(before.allocated_bytes),
            deallocated_bytes: after
                .deallocated_bytes
                .saturating_sub(before.deallocated_bytes),
            live_bytes_delta: signed_delta(after.live_bytes, before.live_bytes),
            peak_live_bytes: after.peak_live_bytes,
        }
    }
}

fn signed_delta(after: u64, before: u64) -> i64 {
    if after >= before {
        i64::try_from(after - before).unwrap_or(i64::MAX)
    } else {
        -i64::try_from(before - after).unwrap_or(i64::MAX)
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
            system_allocations: SystemAllocationMeasurement::between(
                allocations_before.system,
                allocations_after.system,
            ),
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
        system_allocation_calls: distribution(
            iterations
                .iter()
                .map(|item| item.measurement.system_allocations.allocation_calls as f64),
        ),
        system_allocated_bytes: distribution(
            iterations
                .iter()
                .map(|item| item.measurement.system_allocations.allocated_bytes as f64),
        ),
        system_live_bytes_delta: distribution(
            iterations
                .iter()
                .map(|item| item.measurement.system_allocations.live_bytes_delta as f64),
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

fn format_bytes(bytes: u64) -> String {
    const KIB: f64 = 1_024.0;
    const MIB: f64 = KIB * 1_024.0;
    const GIB: f64 = MIB * 1_024.0;
    let bytes = bytes as f64;
    if bytes >= GIB {
        format!("{:.1} GiB", bytes / GIB)
    } else if bytes >= MIB {
        format!("{:.1} MiB", bytes / MIB)
    } else if bytes >= KIB {
        format!("{:.1} KiB", bytes / KIB)
    } else {
        format!("{bytes:.0} B")
    }
}

fn format_signed_bytes(bytes: i64) -> String {
    if bytes < 0 {
        format!("-{}", format_bytes(bytes.unsigned_abs()))
    } else {
        format!("+{}", format_bytes(bytes as u64))
    }
}

fn format_count(count: u64) -> String {
    if count >= 1_000_000 {
        format!("{:.1}m", count as f64 / 1_000_000.0)
    } else if count >= 1_000 {
        format!("{:.1}k", count as f64 / 1_000.0)
    } else {
        count.to_string()
    }
}

fn print_workload(workload: &Workload, build: &PhaseMeasurement, planning: &PhaseMeasurement) {
    println!(
        "Workload\n  {} source + {} lib files | {} | {} nodes | {} queries",
        workload.source_files,
        workload.library_files,
        format_bytes(workload.source_bytes as u64),
        format_count(workload.semantic_nodes as u64),
        workload.checker_queries,
    );
    println!(
        "\nSetup\n  build     {:>7.3} ms\n    arena {:>9} | system {:>9} | live {:>9}",
        build.wall_ms,
        format_bytes(build.arena_bytes_delta as u64),
        format_bytes(build.system_allocations.allocated_bytes),
        format_signed_bytes(build.system_allocations.live_bytes_delta),
    );
    println!(
        "  planning  {:>7.3} ms\n    arena {:>9} | system {:>9} | live {:>9}",
        planning.wall_ms,
        format_bytes(planning.arena_bytes_delta as u64),
        format_bytes(planning.system_allocations.allocated_bytes),
        format_signed_bytes(planning.system_allocations.live_bytes_delta),
    );
}

fn print_checker_census(census: &CheckerCensus) {
    let mut type_kinds = census.type_kinds.iter().collect::<Vec<_>>();
    type_kinds.sort_unstable_by_key(|entry| std::cmp::Reverse(entry.count));
    println!(
        "\nCensus\n  {} types | arena {} / {} allocs\n  system {} / {} allocs | live {}",
        census.registered_types,
        format_bytes(census.arena_bytes as u64),
        census
            .allocations
            .map_or_else(|| "n/a".to_string(), |count| count.to_string()),
        format_bytes(census.system_allocations.allocated_bytes),
        format_count(census.system_allocations.allocation_calls),
        format_signed_bytes(census.system_allocations.live_bytes_delta),
    );
    println!("  Largest type families:");
    for entries in type_kinds.into_iter().take(8).collect::<Vec<_>>().chunks(2) {
        print!("  ");
        for entry in entries {
            print!("  {:<24} {:>5}", entry.kind, entry.count);
        }
        println!();
    }
}

fn print_summary(report: &Report) {
    let wall = &report.summary.wall_ms;
    let cpu = &report.summary.cpu_ms;
    let arena = &report.summary.arena_bytes_delta;
    let system_calls = &report.summary.system_allocation_calls;
    let system_allocated = &report.summary.system_allocated_bytes;
    let system_live = &report.summary.system_live_bytes_delta;
    println!("\nSummary ({} measured passes)", report.iterations.len());
    println!("  {:<8} {:>10} {:>10} {:>10}", "", "median", "p95", "max");
    println!(
        "  {:<8} {:>10} {:>10} {:>10}",
        "wall",
        format!("{:.3} ms", wall.median),
        format!("{:.3} ms", wall.p95),
        format!("{:.3} ms", wall.max),
    );
    println!(
        "  {:<8} {:>10} {:>10} {:>10}",
        "CPU",
        format!("{:.3} ms", cpu.median),
        format!("{:.3} ms", cpu.p95),
        format!("{:.3} ms", cpu.max),
    );
    println!(
        "  {:<8} {:>10} {:>10} {:>10}",
        "arena",
        format_bytes(arena.median as u64),
        format_bytes(arena.p95 as u64),
        format_bytes(arena.max as u64),
    );
    println!(
        "  {:<8} {:>10} {:>10} {:>10}",
        "system",
        format_bytes(system_allocated.median as u64),
        format_bytes(system_allocated.p95 as u64),
        format_bytes(system_allocated.max as u64),
    );
    println!(
        "  {:<8} {:>10} {:>10} {:>10}",
        "allocs",
        format_count(system_calls.median as u64),
        format_count(system_calls.p95 as u64),
        format_count(system_calls.max as u64),
    );
    println!(
        "  {:<8} {:>10} {:>10} {:>10}",
        "live",
        format_signed_bytes(system_live.median as i64),
        format_signed_bytes(system_live.p95 as i64),
        format_signed_bytes(system_live.max as i64),
    );
    println!(
        "  {:<8} {:>10}",
        "peak RSS",
        format_bytes(report.process_after_measurement.peak_rss_bytes),
    );
}
