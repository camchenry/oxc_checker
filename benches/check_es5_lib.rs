use criterion::{Criterion, black_box, criterion_group, criterion_main};
use oxc_allocator::Allocator;
use oxc_checker::{benchmark_support, program};
use std::path::Path;

const ES5_D_TS_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/src/lib/es5.d.ts");
const DOM_D_TS_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/src/lib/dom.generated.d.ts");

fn build_store<'a>(
    allocator: &'a Allocator,
    path: &str,
    name: &str,
) -> (program::ProgramStore<'a>, program::ProgramId) {
    let host = program::FsProgramHost::new();
    let store = program::ProgramStoreBuilder::new(allocator, host)
        .without_default_lib()
        .add_root_file(path)
        .build()
        .unwrap_or_else(|error| {
            panic!("expected {name} to parse and build semantic data: {error}")
        });
    let program_id = store
        .id_for_path(Path::new(path))
        .unwrap_or_else(|| panic!("expected {name} to be present in the program store"));

    (store, program_id)
}

fn bench_check_lib(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    name: &str,
    path: &str,
) {
    let allocator = Allocator::default();
    let (store, program_id) = build_store(&allocator, path, name);
    let plan = benchmark_support::check_plan(&store, program_id);
    let setup_stats = AllocationSnapshot::capture(&allocator);
    let checked_count = benchmark_support::check_program_with_plan(&store, &plan);
    let checked_stats = AllocationSnapshot::capture(&allocator);
    print_allocation_report(name, checked_count, setup_stats, checked_stats);

    group.bench_function(name, |bencher| {
        bencher.iter(|| black_box(benchmark_support::check_program_with_plan(&store, &plan)));
    });
}

#[derive(Clone, Copy)]
struct AllocationSnapshot {
    used_bytes: usize,
    #[cfg(feature = "allocation-stats")]
    allocations: usize,
    #[cfg(feature = "allocation-stats")]
    reallocations: usize,
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

    fn used_bytes_delta(self, earlier: Self) -> usize {
        self.used_bytes.saturating_sub(earlier.used_bytes)
    }
}

fn print_allocation_report(
    name: &str,
    checked_count: usize,
    setup: AllocationSnapshot,
    checked: AllocationSnapshot,
) {
    eprintln!(
        "allocation-stats {name}: setup_used_bytes={} check_delta_used_bytes={} checked_types={checked_count}",
        setup.used_bytes,
        checked.used_bytes_delta(setup),
    );

    #[cfg(feature = "allocation-stats")]
    eprintln!(
        "allocation-stats {name}: setup_allocations={} setup_reallocations={} check_delta_allocations={} check_delta_reallocations={}",
        setup.allocations,
        setup.reallocations,
        checked.allocations.saturating_sub(setup.allocations),
        checked.reallocations.saturating_sub(setup.reallocations),
    );

    #[cfg(not(feature = "allocation-stats"))]
    eprintln!(
        "allocation-stats {name}: allocation counts unavailable; run with `--features 'bench allocation-stats'`"
    );
}

fn bench_check_libs(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("lib_d_ts/check_only");
    group.sample_size(10);
    bench_check_lib(&mut group, "es5", ES5_D_TS_PATH);
    bench_check_lib(&mut group, "dom_generated", DOM_D_TS_PATH);
    group.finish();
}

criterion_group!(benches, bench_check_libs);
criterion_main!(benches);
