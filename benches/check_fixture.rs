use criterion::{Criterion, black_box, criterion_group, criterion_main};
use oxc_allocator::Allocator;
use oxc_checker::{benchmark_support, program};
use std::path::Path;

const MEMBER_EXPRESSION_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/conformance/cases/compiler/memberExpression.ts"
);

#[expect(clippy::expect_used)]
fn bench_member_expression(criterion: &mut Criterion) {
    let allocator = Allocator::default();
    let store = program::ProgramStoreBuilder::new(&allocator, program::FsProgramHost::new())
        .add_root_file(MEMBER_EXPRESSION_PATH)
        .build()
        .expect("memberExpression.ts should parse and build semantic data");
    let program_id = store
        .id_for_path(Path::new(MEMBER_EXPRESSION_PATH))
        .expect("memberExpression.ts should be present in the program store");
    let plan = benchmark_support::check_plan(&store, program_id);

    criterion.bench_function("fixture/check_only/member_expression", |bencher| {
        bencher.iter(|| black_box(benchmark_support::check_program_with_plan(&store, &plan)));
    });
}

criterion_group!(benches, bench_member_expression);
criterion_main!(benches);
