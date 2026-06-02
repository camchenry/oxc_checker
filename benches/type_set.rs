use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use oxc_allocator::Allocator;
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
                    Ty::object(arena, vec![Ty::property("a", ty_number)]),
                    Ty::object(arena, vec![Ty::property("b", ty_string)]),
                    Ty::object(arena, vec![Ty::property("c", ty_boolean)]),
                    Ty::object(arena, vec![Ty::property("d", ty_bigint)]),
                ]
            },
            |ty| reduce_union_type(arena, ty),
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, bench_type_set);
criterion_main!(benches);
