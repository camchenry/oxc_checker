use super::*;
use crate::type_set::UnionAccumulator;
use oxc_allocator::Allocator;
use rustc_hash::{FxHashMap, FxHashSet};

fn arena(allocator: &Allocator) -> CheckerArena<'_> {
    CheckerArena::new(allocator)
}

#[test]
fn type_handles_are_compact() {
    assert_eq!(std::mem::size_of::<Ty<'_>>(), 4);
    assert_eq!(std::mem::size_of::<Option<Ty<'_>>>(), 4);
    assert_eq!(std::mem::size_of::<TypeId>(), 4);
    assert_eq!(std::mem::size_of::<TyObject<'_>>(), 32);
}

#[test]
fn tuple_element_map_ty_preserves_kind() {
    assert_eq!(
        TupleElement::Regular(Ty::string()).map_ty(|_| Ty::number()),
        TupleElement::Regular(Ty::number())
    );
    assert_eq!(
        TupleElement::Rest(Ty::string()).map_ty(|_| Ty::number()),
        TupleElement::Rest(Ty::number())
    );
    assert_eq!(
        TupleElement::Optional(Ty::string()).map_ty(|_| Ty::number()),
        TupleElement::Optional(Ty::number())
    );
}

#[test]
fn name_only_type_references_are_interned() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let first = Ty::type_reference(arena, "Result", [Ty::string()]);
    let second = Ty::type_reference(arena, "Result", [Ty::string()]);
    let hidden_arguments =
        Ty::type_reference_with_display_type_argument_count(arena, "Result", [Ty::string()], 0);

    assert_eq!(first, second);
    assert_ne!(first, hidden_arguments);
}

#[test]
fn visit_type_visits_shared_types_once() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let mut ty = Ty::type_reference(arena, "T", []);
    let mut unique_type_count = 1;
    for _ in 0..32 {
        ty = Ty::tuple(
            arena,
            vec![TupleElement::Regular(ty), TupleElement::Regular(ty)],
        );
        unique_type_count += 1;
    }

    let mut visited = Vec::new();
    visit_type(arena, ty, &mut |ty| visited.push(ty.id()));

    assert_eq!(visited.len(), unique_type_count);
    assert_eq!(
        visited.iter().copied().collect::<FxHashSet<_>>().len(),
        visited.len()
    );
}

#[test]
fn function_predicate_excludes_callable_objects() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let function = Ty::function(
        arena,
        std::iter::empty::<TyTypeParameter>(),
        std::iter::empty::<TyParameter>(),
        Ty::void(),
    );
    let callable_object =
        Ty::object_with_signatures(arena, [], [Signature::new(SignatureKind::Call, function)]);

    assert!(function.is_function(arena));
    assert!(!callable_object.is_function(arena));
}

#[test]
fn object_signatures_render_calls_before_constructs() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let construct_string = Ty::function(arena, [], [], Ty::string());
    let call_number = Ty::function(arena, [], [], Ty::number());
    let construct_boolean = Ty::function(arena, [], [], Ty::boolean());
    let call_bigint = Ty::function(arena, [], [], Ty::bigint());
    let object = Ty::object_with_signatures(
        arena,
        [],
        [
            Signature::new(SignatureKind::Construct, construct_string),
            Signature::new(SignatureKind::Call, call_number),
            Signature::new(SignatureKind::Construct, construct_boolean),
            Signature::new(SignatureKind::Call, call_bigint),
        ],
    );

    assert_eq!(
        object.to_type_string(arena),
        "{ (): number; (): bigint; new (): string; new (): boolean; }"
    );
}

#[test]
fn empty_constructor_object_renders_as_empty_object() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let object = Ty::object_from_slices(arena, &[], &[], &[], true);

    assert_eq!(object.to_type_string(arena), "{}");
}

#[test]
fn instantiated_function_renders_type_parameters_as_arguments() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let type_parameter = Ty::type_parameter("S", Some(Ty::number()), Some(Ty::string()));
    let function = Ty::function_with_type_predicate_and_display(
        arena,
        [type_parameter],
        [],
        Ty::type_reference(arena, "S", std::iter::empty()),
        None,
        true,
    );

    assert_eq!(type_parameter.constraint_type, Some(Ty::number()));
    assert_eq!(function.to_type_string(arena), "<S>() => S");
}

#[test]
fn type_identity_is_recursive_and_distinct_from_handle_identity() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let first = Ty::array(
        arena,
        Ty::object(arena, [Ty::property("value", Ty::string())]),
    );
    let second = Ty::array(
        arena,
        Ty::object(arena, [Ty::property("value", Ty::string())]),
    );
    let different = Ty::array(
        arena,
        Ty::object(arena, [Ty::property("value", Ty::number())]),
    );

    assert_ne!(first, second);
    assert!(arena.is_type_identical_to(first, second));
    assert!(!arena.is_type_identical_to(first, different));

    let mut by_id = FxHashMap::default();
    by_id.insert(first.id(), "first");
    by_id.insert(second.id(), "second");
    assert_eq!(by_id.len(), 2);
    assert_eq!(by_id[&first.id()], "first");
    assert_eq!(by_id[&second.id()], "second");
}

#[test]
fn union_reduction_absorbs_any_and_unknown() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    assert_eq!(Ty::r#union(arena, [Ty::any(), Ty::undefined()]), Ty::any());
    assert_eq!(
        Ty::r#union(arena, [Ty::unknown(), Ty::undefined(), Ty::string()]),
        Ty::unknown()
    );
    assert_eq!(Ty::r#union(arena, [Ty::unknown(), Ty::any()]), Ty::any());
}

#[test]
fn literal_types_are_canonicalized() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    assert_eq!(
        Ty::string_literal(arena, "ready"),
        Ty::string_literal(arena, "ready")
    );
    assert_eq!(
        Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal),
        Ty::number_literal(arena, 1.0, "0x1", NumberBase::Hex)
    );
    assert_eq!(
        Ty::bigint_literal(arena, "1", None, BigintBase::Decimal),
        Ty::bigint_literal(arena, "1", None, BigintBase::Decimal)
    );
    assert_eq!(
        Ty::template_literal(
            arena,
            [TemplateLiteralElement { value: "prefix" }],
            [Ty::string()]
        ),
        Ty::template_literal(
            arena,
            [TemplateLiteralElement { value: "prefix" }],
            [Ty::string()]
        )
    );
}

#[test]
fn derived_types_are_canonicalized() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    let union = Ty::r#union(arena, [Ty::string(), Ty::number()]);
    assert_eq!(
        union,
        Ty::r#union(arena, [Ty::number(), Ty::string()]),
        "union identity uses canonical constituent order"
    );
    assert_eq!(union.to_type_string(arena), "string | number");

    assert_eq!(
        Ty::intersection(arena, [Ty::string(), Ty::primitive_object()]),
        Ty::intersection(arena, [Ty::string(), Ty::primitive_object()])
    );
    assert_eq!(
        Ty::array(arena, Ty::string()),
        Ty::array(arena, Ty::string())
    );
    assert_eq!(
        Ty::tuple(arena, vec![TupleElement::Regular(Ty::string())]),
        Ty::tuple(arena, vec![TupleElement::Regular(Ty::string())])
    );
    assert_eq!(Ty::keyof(arena, union), Ty::keyof(arena, union));
    assert_eq!(
        Ty::indexed_access(arena, union, Ty::string()),
        Ty::indexed_access(arena, union, Ty::string())
    );
}

#[test]
fn union_preserves_distinct_anonymous_object_identities() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let first = Ty::object(arena, [Ty::property("value", Ty::string())]);
    let second = Ty::object(arena, [Ty::property("value", Ty::string())]);

    let union = Ty::r#union(arena, [first, second]);
    let TyKind::Union(union) = arena.ty_kind(union) else {
        panic!("distinct anonymous types should form a union")
    };
    assert_eq!(union.types.as_slice(), &[first, second]);
}

#[test]
fn union_regularizes_structurally_identical_fresh_object_literals() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let first = Ty::object_literal(arena, [Ty::property("value", Ty::string())]);
    let second = Ty::object_literal(arena, [Ty::property("value", Ty::string())]);

    assert_eq!(Ty::r#union(arena, [first, second]), first);
}

#[test]
fn union_reduction_collapses_literals_to_primitive_types() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    assert_eq!(
        Ty::r#union(
            arena,
            [
                Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal),
                Ty::number()
            ]
        ),
        Ty::number()
    );
    assert_eq!(
        Ty::r#union(arena, [Ty::string_literal(arena, "ready"), Ty::string()]),
        Ty::string()
    );
    assert_eq!(
        Ty::r#union(arena, [Ty::boolean_true(), Ty::boolean()]),
        Ty::boolean()
    );
    assert_eq!(
        Ty::r#union(
            arena,
            [
                Ty::bigint_literal(arena, "1", None, BigintBase::Decimal),
                Ty::bigint(),
            ]
        ),
        Ty::bigint()
    );
}

#[test]
fn intersection_reduction_collapses_primitive_to_literal_types() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let number_literal = Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal);
    let string_literal = Ty::string_literal(arena, "ready");
    let bigint_literal = Ty::bigint_literal(arena, "1", None, BigintBase::Decimal);

    assert_eq!(
        Ty::intersection(arena, [Ty::boolean(), Ty::boolean_false()]),
        Ty::boolean_false()
    );
    assert_eq!(
        Ty::intersection(arena, [Ty::boolean_false(), Ty::boolean()]),
        Ty::boolean_false()
    );
    assert_eq!(
        Ty::intersection(arena, [Ty::number(), number_literal]),
        number_literal
    );
    assert_eq!(
        Ty::intersection(arena, [Ty::string(), string_literal]),
        string_literal
    );
    assert_eq!(
        Ty::intersection(arena, [Ty::bigint(), bigint_literal]),
        bigint_literal
    );
}

#[test]
fn empty_object_intersection_removes_nullish_union_members() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let empty_object = Ty::object(arena, []);
    let nullable = Ty::union(arena, [Ty::string(), Ty::null(), Ty::undefined()]);

    assert_eq!(
        Ty::intersection(arena, [nullable, empty_object]),
        Ty::string()
    );
    assert_eq!(
        Ty::intersection(arena, [Ty::never(), empty_object]),
        Ty::never()
    );
    assert_eq!(
        Ty::intersection(arena, [Ty::unknown(), empty_object]),
        empty_object
    );
}

#[test]
fn empty_object_intersection_preserves_unresolved_type_parameters() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let type_parameter = Ty::type_reference(arena, "T", []);
    let empty_object = Ty::object(arena, []);
    let intersection = Ty::intersection(arena, [type_parameter, empty_object]);

    assert!(matches!(
        arena.ty_kind(intersection),
        TyKind::Intersection(_)
    ));
}

#[test]
fn union_reduction_flattens_deduplicates_and_returns_singletons() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let nested = Ty::r#union(arena, [Ty::number(), Ty::string()]);

    let flattened = Ty::r#union(arena, [nested, Ty::number(), Ty::string()]);
    assert!(arena.is_type_identical_to(flattened, nested));
    assert_eq!(
        Ty::r#union(arena, [Ty::number(), Ty::number()]),
        Ty::number()
    );
}

#[test]
fn union_accumulator_completes_empty_and_singleton_inputs() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    assert!(UnionAccumulator::new(arena).is_empty());
    assert_eq!(UnionAccumulator::new(arena).try_build(), None);

    let mut accumulator = UnionAccumulator::new(arena);
    accumulator.add(Ty::string());
    assert!(!accumulator.is_empty());
    assert_eq!(accumulator.try_build(), Some(Ty::string()));
}

#[test]
fn union_accumulator_preserves_canonical_identity_and_flattens_nested_unions() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    let mut first = UnionAccumulator::new(arena);
    first.extend([Ty::number(), Ty::string()]);
    let first = first.build();

    let mut reordered = UnionAccumulator::new(arena);
    reordered.extend([Ty::string(), Ty::number()]);
    assert_eq!(reordered.build(), first);

    let mut nested = UnionAccumulator::new(arena);
    nested.extend([first, Ty::number(), Ty::string()]);
    assert_eq!(nested.build(), first);
}

#[test]
fn union_accumulator_spills_seen_ids_without_changing_members() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let members = (0..20)
        .map(|value| Ty::number_literal(arena, f64::from(value), "0", NumberBase::Decimal))
        .collect::<Vec<_>>();

    let mut accumulator = UnionAccumulator::new(arena);
    accumulator.extend(members.iter().copied());
    accumulator.extend(members.iter().copied());
    let union = accumulator.build();

    let TyKind::Union(union) = arena.ty_kind(union) else {
        panic!("twenty distinct literals should produce a union");
    };
    assert_eq!(union.types.as_slice(), members);
}

#[test]
fn union_reduction_preserves_distinct_non_redundant_types() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    assert_eq!(
        Ty::r#union(arena, [Ty::number(), Ty::undefined()]).to_type_string(arena),
        "number | undefined"
    );
    assert_eq!(
        Ty::r#union(arena, [Ty::void(), Ty::undefined()]).to_type_string(arena),
        "void | undefined"
    );
}

#[test]
fn union_reduction_removes_never_from_multi_member_unions() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    assert_eq!(
        Ty::r#union(arena, [Ty::never(), Ty::undefined()]),
        Ty::undefined()
    );
    assert_eq!(Ty::r#union(arena, [Ty::never()]), Ty::never());
}

#[test]
fn union_reduction_absorbs_literals_contained_by_template_literals() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let literal_template =
        arena.alloc_type(TyKind::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter([TemplateLiteralElement { value: "test" }]),
            expressions: arena.vec_from_iter([]),
        })));
    let pattern_template =
        arena.alloc_type(TyKind::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter([
                TemplateLiteralElement { value: "test" },
                TemplateLiteralElement { value: "" },
            ]),
            expressions: arena.vec_from_iter([Ty::string()]),
        })));

    assert_eq!(
        Ty::r#union(arena, [literal_template, pattern_template]).to_type_string(arena),
        "`test${string}`"
    );
    assert_eq!(
        Ty::r#union(arena, [Ty::string_literal(arena, "test"), pattern_template])
            .to_type_string(arena),
        "`test${string}`"
    );

    let backtracking_template =
        arena.alloc_type(TyKind::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter([
                TemplateLiteralElement { value: "" },
                TemplateLiteralElement { value: "a" },
                TemplateLiteralElement { value: "" },
            ]),
            expressions: arena.vec_from_iter([Ty::string(), Ty::string_literal(arena, "b")]),
        })));
    assert_eq!(
        Ty::r#union(
            arena,
            [Ty::string_literal(arena, "aab"), backtracking_template]
        )
        .to_type_string(arena),
        "`${string}a${\"b\"}`"
    );
}

#[test]
fn union_display_parenthesizes_function_members() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let a1 = Ty::type_reference(arena, "A1", []);
    let r = Ty::type_reference(arena, "R", []);
    let function = Ty::function(arena, [], [Ty::parameter("arg1", a1)], r);

    assert_eq!(
        Ty::r#union(arena, [function, Ty::null(), Ty::undefined()]).to_type_string(arena),
        "((arg1: A1) => R) | null | undefined"
    );
}

#[test]
fn object_method_display_uses_signature_syntax() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let abort_signal = Ty::type_reference(arena, "AbortSignal", []);
    let abort = TyProperty {
        name: "abort",
        flags: TyPropertyFlags::NONE,
        ty: Ty::function(
            arena,
            [],
            [Ty::optional_parameter("reason", Ty::any())],
            abort_signal,
        ),
        computed: false,
        optional: false,
        method: true,
        readonly: false,
    };

    assert_eq!(
        Ty::object(arena, [abort]).to_type_string(arena),
        "{ abort(reason?: any): AbortSignal; }"
    );
}

#[test]
fn object_readonly_property_display() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let readonly = TyProperty {
        name: "x",
        flags: TyPropertyFlags::NONE,
        ty: Ty::string(),
        computed: false,
        optional: false,
        method: false,
        readonly: true,
    };

    assert_eq!(
        Ty::object(arena, [readonly]).to_type_string(arena),
        "{ readonly x: string; }"
    );
}

#[test]
fn object_non_identifier_property_uses_single_quotes() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let property = TyProperty {
        name: "~types",
        flags: TyPropertyFlags::SINGLE_QUOTED,
        ty: Ty::string(),
        computed: false,
        optional: true,
        method: false,
        readonly: true,
    };

    assert_eq!(
        Ty::object(arena, [property]).to_type_string(arena),
        "{ readonly '~types'?: string; }"
    );
}

#[test]
fn object_non_identifier_property_preserves_double_quotes() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let property = TyProperty {
        name: "data-id",
        flags: TyPropertyFlags::NONE,
        ty: Ty::string(),
        computed: false,
        optional: false,
        method: false,
        readonly: false,
    };

    assert_eq!(
        Ty::object(arena, [property]).to_type_string(arena),
        "{ \"data-id\": string; }"
    );
}

#[test]
fn object_property_type_preserves_single_quotes() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let property = TyProperty {
        name: "brand",
        flags: TyPropertyFlags::TYPE_SINGLE_QUOTED,
        ty: Ty::string_literal(arena, "test-brand"),
        computed: false,
        optional: false,
        method: false,
        readonly: false,
    };

    assert_eq!(
        Ty::object(arena, [property]).to_type_string(arena),
        "{ brand: 'test-brand'; }"
    );
}

#[test]
fn nested_object_property_uses_default_double_quotes() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let nested = Ty::object(
        arena,
        [TyProperty {
            name: "stage-0",
            flags: TyPropertyFlags::SINGLE_QUOTED,
            ty: Ty::string(),
            computed: false,
            optional: false,
            method: false,
            readonly: false,
        }],
    );
    let outer = Ty::object(
        arena,
        [TyProperty {
            name: "configs",
            flags: TyPropertyFlags::NONE,
            ty: nested,
            computed: false,
            optional: false,
            method: false,
            readonly: false,
        }],
    );

    assert_eq!(
        outer.to_type_string(arena),
        "{ configs: { \"stage-0\": string; }; }"
    );
}

#[test]
fn object_property_preserves_generic_array_declaration_syntax() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let array = Ty::generic_array(arena, Ty::string(), false);
    let values = TyProperty {
        name: "values",
        flags: TyPropertyFlags::NONE,
        ty: array,
        computed: false,
        optional: true,
        method: false,
        readonly: false,
    };
    let maybe_values = TyProperty {
        name: "maybeValues",
        flags: TyPropertyFlags::NONE,
        ty: Ty::union(arena, [array, Ty::undefined()]),
        computed: false,
        optional: false,
        method: false,
        readonly: false,
    };

    assert_eq!(array.to_type_string(arena), "string[]");
    assert_eq!(
        Ty::object(arena, [values, maybe_values]).to_type_string(arena),
        "{ values?: Array<string>; maybeValues: Array<string> | undefined; }"
    );
    assert_eq!(
        Ty::function(arena, [], [], array).to_type_string(arena),
        "() => Array<string>"
    );
}
