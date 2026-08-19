use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use oxc_allocator::Allocator;
use oxc_ast::ast::NumberBase;
use oxc_checker::{CheckerArena, Ty, type_set::reduce_union_type};

fn bench_type_set(criterion: &mut Criterion) {
    let allocator = Allocator::default();
    let arena = CheckerArena::new(&allocator);
    let ty_string = Ty::string();
    let ty_number = Ty::number();
    let ty_boolean = Ty::boolean();
    let ty_bigint = Ty::bigint();
    let ty_null = Ty::null();
    let ty_undefined = Ty::undefined();
    let ty_never = Ty::never();
    let ty_any = Ty::any();
    criterion.bench_function("reduce_union_type_primitives", |b| {
        b.iter(|| reduce_union_type(arena, [ty_string, ty_number, ty_boolean, ty_bigint]))
    });
    criterion.bench_function("reduce_union_type_with_null_and_undefined", |b| {
        b.iter(|| {
            reduce_union_type(
                arena,
                [
                    ty_string,
                    ty_number,
                    ty_boolean,
                    ty_bigint,
                    ty_null,
                    ty_undefined,
                ],
            )
        })
    });
    criterion.bench_function("reduce_union_type_with_never", |b| {
        b.iter(|| {
            reduce_union_type(
                arena,
                [
                    ty_string,
                    ty_number,
                    ty_boolean,
                    ty_bigint,
                    ty_null,
                    ty_undefined,
                    ty_never,
                ],
            )
        })
    });
    criterion.bench_function("reduce_union_type_with_any", |b| {
        b.iter(|| {
            reduce_union_type(
                arena,
                [
                    ty_string,
                    ty_number,
                    ty_boolean,
                    ty_bigint,
                    ty_null,
                    ty_undefined,
                    ty_never,
                    ty_any,
                ],
            )
        })
    });
    criterion.bench_function("reduce_union_type_with_objects", |b| {
        b.iter_batched(
            || {
                vec![
                    arena.object(vec![Ty::property("a", ty_number)]),
                    arena.object(vec![Ty::property("b", ty_string)]),
                    arena.object(vec![Ty::property("c", ty_boolean)]),
                    arena.object(vec![Ty::property("d", ty_bigint)]),
                ]
            },
            |ty| reduce_union_type(arena, ty),
            BatchSize::SmallInput,
        )
    });

    let distinct_types = (0..256)
        .map(|index| arena.number_literal(index as f64, "0", NumberBase::Decimal))
        .collect::<Vec<_>>();
    let mut distinct_group = criterion.benchmark_group("reduce_union_type/distinct");
    for size in [2, 4, 8, 16, 64, 256] {
        let types = &distinct_types[..size];
        distinct_group.throughput(Throughput::Elements(size as u64));
        distinct_group.bench_with_input(BenchmarkId::from_parameter(size), types, |b, types| {
            b.iter(|| reduce_union_type(arena, types.iter().copied()))
        });
    }
    distinct_group.finish();

    let mut duplicates_group = criterion.benchmark_group("reduce_union_type/duplicates");
    for size in [8, 64, 256] {
        let types = (0..size)
            .map(|index| distinct_types[index % 4])
            .collect::<Vec<_>>();
        duplicates_group.throughput(Throughput::Elements(size as u64));
        duplicates_group.bench_with_input(BenchmarkId::from_parameter(size), &types, |b, types| {
            b.iter(|| reduce_union_type(arena, types.iter().copied()))
        });
    }
    duplicates_group.finish();

    let nested = distinct_types
        .chunks_exact(4)
        .take(16)
        .map(|types| arena.union(types.iter().copied()))
        .collect::<Vec<_>>();
    let mut nested_group = criterion.benchmark_group("reduce_union_type/nested");
    for size in [2, 4, 8, 16] {
        let types = &nested[..size];
        nested_group.throughput(Throughput::Elements((size * 4) as u64));
        nested_group.bench_with_input(BenchmarkId::from_parameter(size * 4), types, |b, types| {
            b.iter(|| reduce_union_type(arena, types.iter().copied()))
        });
    }
    nested_group.finish();
}

criterion_group!(benches, bench_type_set);
criterion_main!(benches);
