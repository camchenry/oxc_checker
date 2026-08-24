use super::*;
use crate::type_set::UnionAccumulator;
use crate::{
    checker::Checker,
    program::{FsProgramHost, ProgramStore, ProgramStoreBuilder},
};
use oxc_allocator::Allocator;
use rustc_hash::{FxHashMap, FxHashSet};

fn arena(allocator: &Allocator) -> CheckerArena<'_> {
    CheckerArena::new(allocator)
}

struct TypeStringContext<'a> {
    store: ProgramStore<'a>,
    arena: CheckerArena<'a>,
}

impl<'a> TypeStringContext<'a> {
    fn new(allocator: &'a Allocator) -> Self {
        let store = ProgramStoreBuilder::new(allocator, FsProgramHost::new())
            .without_default_lib()
            .build()
            .unwrap();
        let arena = CheckerArena::new(store.allocator());
        Self { store, arena }
    }

    fn type_string(&self, ty: Ty<'a>) -> String {
        Checker::with_arena(&self.store, self.arena).to_type_string(ty)
    }
}

#[test]
fn type_handles_are_compact() {
    assert_eq!(std::mem::size_of::<Ty<'_>>(), 4);
    assert_eq!(std::mem::size_of::<Option<Ty<'_>>>(), 4);
    assert_eq!(std::mem::size_of::<TypeId>(), 4);
    assert_eq!(std::mem::size_of::<TyObject<'_>>(), 32);
    assert_eq!(std::mem::size_of::<TyTuple<'_>>(), 48);
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
fn tuple_labels_are_aligned_and_stored_only_when_present() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let unlabeled = arena.tuple(vec![
        TupleElement::Regular(Ty::string()),
        TupleElement::Optional(Ty::number()),
    ]);
    let labeled = arena.tuple_with_labels(
        [
            LabeledTupleElement::new(TupleElement::Regular(Ty::string()), Some("name")),
            LabeledTupleElement::unlabeled(TupleElement::Optional(Ty::number())),
        ],
        TupleReadonly::Mutable,
    );
    let explicitly_unlabeled = arena.tuple_with_labels(
        [
            LabeledTupleElement::unlabeled(TupleElement::Regular(Ty::string())),
            LabeledTupleElement::unlabeled(TupleElement::Optional(Ty::number())),
        ],
        TupleReadonly::Mutable,
    );
    let spread_labeled = arena.tuple_with_labels(
        [
            LabeledTupleElement::unlabeled(TupleElement::Regular(Ty::boolean())),
            LabeledTupleElement::unlabeled(TupleElement::Rest(labeled)),
            LabeledTupleElement::unlabeled(TupleElement::Regular(Ty::bigint())),
        ],
        TupleReadonly::Mutable,
    );

    assert_eq!(unlabeled, explicitly_unlabeled);

    let TyKind::Tuple(unlabeled) = arena.ty_kind(unlabeled) else {
        panic!("expected tuple");
    };
    assert!(unlabeled.labels().is_none());

    let TyKind::Tuple(labeled) = arena.ty_kind(labeled) else {
        panic!("expected tuple");
    };
    assert_eq!(
        labeled.labeled_elements().collect::<Vec<_>>(),
        [
            LabeledTupleElement::new(TupleElement::Regular(Ty::string()), Some("name")),
            LabeledTupleElement::unlabeled(TupleElement::Optional(Ty::number())),
        ]
    );

    let TyKind::Tuple(spread_labeled) = arena.ty_kind(spread_labeled) else {
        panic!("expected tuple");
    };
    assert_eq!(
        spread_labeled.labels(),
        Some([None, Some("name"), None, None].as_slice())
    );
}

#[test]
fn name_only_type_references_are_interned() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let first = arena.type_reference("Result", [Ty::string()]);
    let second = arena.type_reference("Result", [Ty::string()]);
    let hidden_arguments =
        arena.type_reference_with_display_type_argument_count("Result", [Ty::string()], 0);

    assert_eq!(first, second);
    assert_ne!(first, hidden_arguments);
}

#[test]
fn visit_type_visits_shared_types_once() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let mut ty = arena.type_reference("T", []);
    let mut unique_type_count = 1;
    for _ in 0..32 {
        ty = arena.tuple(vec![TupleElement::Regular(ty), TupleElement::Regular(ty)]);
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
    let function = arena.function(
        std::iter::empty::<TyTypeParameter>(),
        std::iter::empty::<TyParameter>(),
        Ty::void(),
    );
    let callable_object =
        arena.object_with_signatures([], [Signature::new(SignatureKind::Call, function)]);

    assert!(function.is_function(arena));
    assert!(!callable_object.is_function(arena));
}

#[test]
fn object_signatures_render_calls_before_constructs() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
    let construct_string = arena.function([], [], Ty::string());
    let call_number = arena.function([], [], Ty::number());
    let construct_boolean = arena.function([], [], Ty::boolean());
    let call_bigint = arena.function([], [], Ty::bigint());
    let object = arena.object_with_signatures(
        [],
        [
            Signature::new(SignatureKind::Construct, construct_string),
            Signature::new(SignatureKind::Call, call_number),
            Signature::new(SignatureKind::Construct, construct_boolean),
            Signature::new(SignatureKind::Call, call_bigint),
        ],
    );

    assert_eq!(
        context.type_string(object),
        "{ (): number; (): bigint; new (): string; new (): boolean; }"
    );
}

#[test]
fn empty_constructor_object_renders_as_empty_object() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
    let object = arena.object_from_slices(&[], &[], &[], true);

    assert_eq!(context.type_string(object), "{}");
}

#[test]
fn instantiated_function_renders_type_parameters_as_arguments() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
    let type_parameter = Ty::type_parameter("S", Some(Ty::number()), Some(Ty::string()));
    let function = arena.function_with_type_predicate_and_display(
        [type_parameter],
        [],
        arena.type_reference("S", std::iter::empty()),
        None,
        true,
    );

    assert_eq!(type_parameter.constraint_type, Some(Ty::number()));
    assert_eq!(context.type_string(function), "<S>() => S");
}

#[test]
fn type_identity_is_recursive_and_distinct_from_handle_identity() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let first = arena.array(arena.object([Ty::property("value", Ty::string())]));
    let second = arena.array(arena.object([Ty::property("value", Ty::string())]));
    let different = arena.array(arena.object([Ty::property("value", Ty::number())]));

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

    assert_eq!(arena.union([Ty::any(), Ty::undefined()]), Ty::any());
    assert_eq!(
        arena.union([Ty::unknown(), Ty::undefined(), Ty::string()]),
        Ty::unknown()
    );
    assert_eq!(arena.union([Ty::unknown(), Ty::any()]), Ty::any());
}

#[test]
fn literal_types_are_canonicalized() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    assert_eq!(arena.string_literal("ready"), arena.string_literal("ready"));
    assert_eq!(
        arena.number_literal(1.0, "1", NumberBase::Decimal),
        arena.number_literal(1.0, "0x1", NumberBase::Hex)
    );
    assert_eq!(
        arena.bigint_literal("1", None, BigintBase::Decimal),
        arena.bigint_literal("1", None, BigintBase::Decimal)
    );
    assert_eq!(
        arena.template_literal([TemplateLiteralElement { value: "prefix" }], [Ty::string()]),
        arena.template_literal([TemplateLiteralElement { value: "prefix" }], [Ty::string()])
    );
}

#[test]
fn derived_types_are_canonicalized() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;

    let union = arena.union([Ty::string(), Ty::number()]);
    assert_eq!(
        union,
        arena.union([Ty::number(), Ty::string()]),
        "union identity uses canonical constituent order"
    );
    assert_eq!(context.type_string(union), "string | number");

    assert_eq!(
        arena.intersection([Ty::string(), Ty::primitive_object()]),
        arena.intersection([Ty::string(), Ty::primitive_object()])
    );
    assert_eq!(arena.array(Ty::string()), arena.array(Ty::string()));
    assert_eq!(
        arena.tuple(vec![TupleElement::Regular(Ty::string())]),
        arena.tuple(vec![TupleElement::Regular(Ty::string())])
    );
    assert_eq!(arena.keyof(union), arena.keyof(union));
    assert_eq!(
        arena.indexed_access(union, Ty::string()),
        arena.indexed_access(union, Ty::string())
    );
}

#[test]
fn union_preserves_distinct_anonymous_object_identities() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let first = arena.object([Ty::property("value", Ty::string())]);
    let second = arena.object([Ty::property("value", Ty::string())]);

    let union = arena.union([first, second]);
    let TyKind::Union(union) = arena.ty_kind(union) else {
        panic!("distinct anonymous types should form a union")
    };
    assert_eq!(union.types.as_slice(), &[first, second]);
}

#[test]
fn union_regularizes_structurally_identical_fresh_object_literals() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let first = arena.object_literal([Ty::property("value", Ty::string())]);
    let second = arena.object_literal([Ty::property("value", Ty::string())]);

    assert_eq!(arena.union([first, second]), first);
}

#[test]
fn union_reduction_collapses_literals_to_primitive_types() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    assert_eq!(
        arena.union([
            arena.number_literal(1.0, "1", NumberBase::Decimal),
            Ty::number()
        ]),
        Ty::number()
    );
    assert_eq!(
        arena.union([arena.string_literal("ready"), Ty::string()]),
        Ty::string()
    );
    assert_eq!(
        arena.union([Ty::boolean_true(), Ty::boolean()]),
        Ty::boolean()
    );
    assert_eq!(
        arena.union([
            arena.bigint_literal("1", None, BigintBase::Decimal),
            Ty::bigint(),
        ]),
        Ty::bigint()
    );
}

#[test]
fn intersection_reduction_collapses_primitive_to_literal_types() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let number_literal = arena.number_literal(1.0, "1", NumberBase::Decimal);
    let string_literal = arena.string_literal("ready");
    let bigint_literal = arena.bigint_literal("1", None, BigintBase::Decimal);

    assert_eq!(
        arena.intersection([Ty::boolean(), Ty::boolean_false()]),
        Ty::boolean_false()
    );
    assert_eq!(
        arena.intersection([Ty::boolean_false(), Ty::boolean()]),
        Ty::boolean_false()
    );
    assert_eq!(
        arena.intersection([Ty::number(), number_literal]),
        number_literal
    );
    assert_eq!(
        arena.intersection([Ty::string(), string_literal]),
        string_literal
    );
    assert_eq!(
        arena.intersection([Ty::bigint(), bigint_literal]),
        bigint_literal
    );
}

#[test]
fn empty_object_intersection_removes_nullish_union_members() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let empty_object = arena.object([]);
    let nullable = arena.union([Ty::string(), Ty::null(), Ty::undefined()]);

    assert_eq!(arena.intersection([nullable, empty_object]), Ty::string());
    assert_eq!(arena.intersection([Ty::never(), empty_object]), Ty::never());
    assert_eq!(
        arena.intersection([Ty::unknown(), empty_object]),
        empty_object
    );
}

#[test]
fn empty_object_intersection_preserves_unresolved_type_parameters() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let type_parameter = arena.type_reference("T", []);
    let empty_object = arena.object([]);
    let intersection = arena.intersection([type_parameter, empty_object]);

    assert!(matches!(
        arena.ty_kind(intersection),
        TyKind::Intersection(_)
    ));
}

#[test]
fn union_reduction_flattens_deduplicates_and_returns_singletons() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);
    let nested = arena.union([Ty::number(), Ty::string()]);

    let flattened = arena.union([nested, Ty::number(), Ty::string()]);
    assert!(arena.is_type_identical_to(flattened, nested));
    assert_eq!(arena.union([Ty::number(), Ty::number()]), Ty::number());
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
        .map(|value| arena.number_literal(f64::from(value), "0", NumberBase::Decimal))
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
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;

    assert_eq!(
        context.type_string(arena.union([Ty::number(), Ty::undefined()])),
        "number | undefined"
    );
    assert_eq!(
        context.type_string(arena.union([Ty::void(), Ty::undefined()])),
        "void | undefined"
    );
}

#[test]
fn union_reduction_removes_never_from_multi_member_unions() {
    let allocator = Allocator::default();
    let arena = arena(&allocator);

    assert_eq!(arena.union([Ty::never(), Ty::undefined()]), Ty::undefined());
    assert_eq!(arena.union([Ty::never()]), Ty::never());
}

#[test]
fn union_reduction_absorbs_literals_contained_by_template_literals() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
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
        context.type_string(arena.union([literal_template, pattern_template])),
        "`test${string}`"
    );
    assert_eq!(
        context.type_string(arena.union([arena.string_literal("test"), pattern_template])),
        "`test${string}`"
    );

    let backtracking_template =
        arena.alloc_type(TyKind::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter([
                TemplateLiteralElement { value: "" },
                TemplateLiteralElement { value: "a" },
                TemplateLiteralElement { value: "" },
            ]),
            expressions: arena.vec_from_iter([Ty::string(), arena.string_literal("b")]),
        })));
    assert_eq!(
        context.type_string(arena.union([arena.string_literal("aab"), backtracking_template])),
        "`${string}a${\"b\"}`"
    );
}

#[test]
fn union_display_parenthesizes_function_members() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
    let a1 = arena.type_reference("A1", []);
    let r = arena.type_reference("R", []);
    let function = arena.function([], [Ty::parameter("arg1", a1)], r);

    assert_eq!(
        context.type_string(arena.union([function, Ty::null(), Ty::undefined()])),
        "((arg1: A1) => R) | null | undefined"
    );
}

#[test]
fn conditional_display_parenthesizes_conditional_return_of_function_extends_type() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
    let conditional = arena.conditional(
        arena.type_reference("T", []),
        Ty::string(),
        Ty::number(),
        Ty::boolean(),
        true,
    );
    let function = arena.function([], [], conditional);
    let other_conditional = arena.conditional(
        arena.type_reference("U", []),
        Ty::string(),
        Ty::number(),
        Ty::boolean(),
        true,
    );
    let other_function = arena.function([], [], other_conditional);
    let outer_conditional = arena.conditional(
        function,
        other_function,
        Ty::boolean_true(),
        Ty::never(),
        true,
    );

    assert_eq!(
        context.type_string(outer_conditional),
        "(() => T extends string ? number : boolean) extends () => (U extends string ? number : boolean) ? true : never"
    );
}

#[test]
fn object_method_display_uses_signature_syntax() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
    let abort_signal = arena.type_reference("AbortSignal", []);
    let abort = TyProperty {
        name: "abort",
        flags: TyPropertyFlags::NONE,
        ty: arena.function(
            [],
            [Ty::parameter("reason", Ty::any()).optional(true)],
            abort_signal,
        ),
        computed: false,
        optional: false,
        method: true,
        readonly: false,
    };

    assert_eq!(
        context.type_string(arena.object([abort])),
        "{ abort(reason?: any): AbortSignal; }"
    );
}

#[test]
fn object_readonly_property_display() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
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
        context.type_string(arena.object([readonly])),
        "{ readonly x: string; }"
    );
}

#[test]
fn object_non_identifier_property_uses_single_quotes() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
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
        context.type_string(arena.object([property])),
        "{ readonly '~types'?: string; }"
    );
}

#[test]
fn object_non_identifier_property_preserves_double_quotes() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
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
        context.type_string(arena.object([property])),
        "{ \"data-id\": string; }"
    );
}

#[test]
fn object_property_type_preserves_single_quotes() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
    let property = TyProperty {
        name: "brand",
        flags: TyPropertyFlags::TYPE_SINGLE_QUOTED,
        ty: arena.string_literal("test-brand"),
        computed: false,
        optional: false,
        method: false,
        readonly: false,
    };

    assert_eq!(
        context.type_string(arena.object([property])),
        "{ brand: 'test-brand'; }"
    );
}

#[test]
fn nested_object_property_uses_default_double_quotes() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
    let nested = arena.object([TyProperty {
        name: "stage-0",
        flags: TyPropertyFlags::SINGLE_QUOTED,
        ty: Ty::string(),
        computed: false,
        optional: false,
        method: false,
        readonly: false,
    }]);
    let outer = arena.object([TyProperty {
        name: "configs",
        flags: TyPropertyFlags::NONE,
        ty: nested,
        computed: false,
        optional: false,
        method: false,
        readonly: false,
    }]);

    assert_eq!(
        context.type_string(outer),
        "{ configs: { \"stage-0\": string; }; }"
    );
}

#[test]
fn object_property_preserves_generic_array_declaration_syntax() {
    let allocator = Allocator::default();
    let context = TypeStringContext::new(&allocator);
    let arena = context.arena;
    let array = arena.generic_array(Ty::string(), false);
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
        ty: arena.union([array, Ty::undefined()]),
        computed: false,
        optional: false,
        method: false,
        readonly: false,
    };

    assert_eq!(context.type_string(array), "string[]");
    assert_eq!(
        context.type_string(arena.object([values, maybe_values])),
        "{ values?: Array<string>; maybeValues: Array<string> | undefined; }"
    );
    assert_eq!(
        context.type_string(arena.function([], [], array)),
        "() => Array<string>"
    );
}
