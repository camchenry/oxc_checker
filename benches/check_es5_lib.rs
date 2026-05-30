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

    group.bench_function(name, |bencher| {
        bencher.iter(|| black_box(benchmark_support::check_program_with_plan(&store, &plan)));
    });
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
