use oxc_allocator::Allocator;
use oxc_ast::ast::NumberBase;
use std::{
    borrow::Cow,
    path::{Path, PathBuf},
};

use super::*;
use crate::{
    checker::Checker,
    program::{HostModuleResolution, ProgramHost, ProgramStore, ProgramStoreBuilder},
    types::CheckerArena,
};

struct TestProgramHost;

impl ProgramHost for TestProgramHost {
    fn read_source(&self, _path: &Path) -> crate::program::ProgramStoreResult<Cow<'_, str>> {
        Ok(Cow::Borrowed(""))
    }

    fn canonicalize_path(&self, path: &Path) -> PathBuf {
        path.to_path_buf()
    }

    fn resolve_module(&self, _containing_file: &Path, specifier: &str) -> HostModuleResolution {
        HostModuleResolution::Missing(specifier.to_string())
    }
}

fn test_store<'a>(allocator: &'a Allocator) -> ProgramStore<'a> {
    ProgramStoreBuilder::new(allocator, TestProgramHost)
        .add_root_file("/test.ts")
        .without_default_lib()
        .build()
        .unwrap()
}

macro_rules! test_checker {
    ($allocator:ident, $store:ident, $checker:ident, $arena:ident) => {
        let $store = test_store(&$allocator);
        let $checker = Checker::new(&$store);
        let $arena = $checker.arena;
    };
}

fn assert_optional_type_eq<'a>(
    arena: CheckerArena<'a>,
    left: Option<Ty<'a>>,
    right: Option<Ty<'a>>,
) {
    let identical = match (left, right) {
        (Some(left), Some(right)) => arena.is_type_identical_to(left, right),
        (None, None) => true,
        _ => false,
    };
    assert!(identical, "type structures differ: {left:?} != {right:?}");
}

#[test]
fn resolves_dependent_default_when_only_dependent_parameter_is_read() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter_t = Ty::type_parameter("T", None, Some(Ty::string()));
    let type_parameter_u = Ty::type_parameter(
        "U",
        None,
        Some(arena.type_reference("T", std::iter::empty())),
    );
    let mut context = InferenceContext::with_substitutions(
        [type_parameter_t, type_parameter_u],
        &TypeParameterSubstitutions::new(),
        arena,
    );

    assert_eq!(
        context.resolve_type_parameter_by_name("U", &checker, InferenceResolutionFlags::NONE,),
        Some(Ty::string()),
    );
    assert!(context.inferences[0].is_fixed);
    assert!(context.inferences[1].is_fixed);
}

#[test]
fn resolving_type_parameter_fixes_it_before_dependent_default() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter_t = Ty::type_parameter("T", None, None);
    let type_parameter_u = Ty::type_parameter(
        "U",
        None,
        Some(arena.type_reference("T", std::iter::empty())),
    );
    let mut context = InferenceContext::with_substitutions(
        [type_parameter_t, type_parameter_u],
        &TypeParameterSubstitutions::new(),
        arena,
    );
    context.add_candidate(
        type_parameter_t,
        Ty::number(),
        InferencePriority::NakedTypeVariable,
        InferenceVariance::Covariant,
    );

    assert_eq!(
        context.resolve_type_parameter_by_name("T", &checker, InferenceResolutionFlags::NONE,),
        Some(Ty::number()),
    );
    assert!(context.inferences[0].is_fixed);
    assert_eq!(
        context.resolve_type_parameter_by_name("U", &checker, InferenceResolutionFlags::NONE,),
        Some(Ty::number()),
    );
    assert!(context.inferences[1].is_fixed);
}

#[test]
fn contextual_mapper_resolves_dependent_default_on_read() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter_t = Ty::type_parameter("T", None, Some(Ty::string()));
    let type_parameter_u = Ty::type_parameter(
        "U",
        None,
        Some(arena.type_reference("T", std::iter::empty())),
    );
    let context = InferenceContext::with_substitutions(
        [type_parameter_t, type_parameter_u],
        &TypeParameterSubstitutions::new(),
        arena,
    );
    let resolution =
        context.resolve_with_contextual_mapper(&checker, InferenceResolutionFlags::NONE);

    assert_eq!(
        resolution
            .mapper()
            .map(arena, arena.type_reference("U", std::iter::empty()),),
        Ty::string(),
    );
}

#[test]
fn indexed_access_inference_simplifies_when_index_candidate_is_known() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter_t = Ty::type_parameter("T", None, None);
    let type_parameter_k = Ty::type_parameter("K", Some(arena.string_literal("value")), None);
    let mut context = InferenceContext::with_substitutions(
        [type_parameter_t, type_parameter_k],
        &TypeParameterSubstitutions::new(),
        arena,
    )
    .with_return_type(arena.type_reference("T", std::iter::empty()));
    context.add_candidate(
        type_parameter_k,
        arena.string_literal("value"),
        InferencePriority::NakedTypeVariable,
        InferenceVariance::Covariant,
    );

    checker.infer_types(
        arena.indexed_access(
            arena.object([Ty::property(
                "value",
                arena.type_reference("T", std::iter::empty()),
            )]),
            arena.type_reference("K", std::iter::empty()),
        ),
        Ty::number(),
        &mut context,
    );

    assert_eq!(
        context.resolve_type_parameter_by_name("T", &checker, InferenceResolutionFlags::NONE,),
        Some(Ty::number()),
    );
}

#[test]
fn indexed_access_inference_preserves_unresolved_shape_without_index_candidate() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter_t = Ty::type_parameter("T", None, None);
    let type_parameter_k = Ty::type_parameter("K", Some(arena.string_literal("value")), None);
    let mut context = InferenceContext::with_substitutions(
        [type_parameter_t, type_parameter_k],
        &TypeParameterSubstitutions::new(),
        arena,
    )
    .with_return_type(arena.type_reference("T", std::iter::empty()));

    checker.infer_types(
        arena.indexed_access(
            arena.object([Ty::property(
                "value",
                arena.type_reference("T", std::iter::empty()),
            )]),
            arena.type_reference("K", std::iter::empty()),
        ),
        Ty::number(),
        &mut context,
    );

    assert_eq!(context.inferences[0].candidates, Vec::<Ty<'_>>::new());
}

#[test]
fn covariant_candidates_use_common_supertype_without_combination_priority() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter = Ty::type_parameter("T", None, None);
    let mut context = InferenceContext::with_substitutions(
        [type_parameter],
        &TypeParameterSubstitutions::new(),
        arena,
    )
    .with_return_type(arena.type_reference("Result", std::iter::empty()));
    context.add_candidate(
        type_parameter,
        arena.string_literal("ready"),
        InferencePriority::Low,
        InferenceVariance::Covariant,
    );
    context.add_candidate(
        type_parameter,
        arena.number_literal(1.0, "1", NumberBase::Decimal),
        InferencePriority::Low,
        InferenceVariance::Covariant,
    );

    assert_optional_type_eq(
        arena,
        context.get_inferred_type(0, &checker),
        Some(arena.string_literal("ready")),
    );
}

#[test]
fn covariant_candidates_combine_for_naked_type_variable_priority() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter = Ty::type_parameter("T", None, None);
    let mut context = InferenceContext::with_substitutions(
        [type_parameter],
        &TypeParameterSubstitutions::new(),
        arena,
    );
    context.add_candidate(
        type_parameter,
        arena.string_literal("ready"),
        InferencePriority::NakedTypeVariable,
        InferenceVariance::Covariant,
    );
    context.add_candidate(
        type_parameter,
        arena.number_literal(1.0, "1", NumberBase::Decimal),
        InferencePriority::NakedTypeVariable,
        InferenceVariance::Covariant,
    );

    assert_optional_type_eq(
        arena,
        context.get_inferred_type(0, &checker),
        Some(arena.union([
            arena.string_literal("ready"),
            arena.number_literal(1.0, "1", NumberBase::Decimal),
        ])),
    );
}

#[test]
fn top_level_literal_candidates_widen_when_not_top_level_in_return() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter = Ty::type_parameter("T", None, None);
    let mut context = InferenceContext::with_substitutions(
        [type_parameter],
        &TypeParameterSubstitutions::new(),
        arena,
    )
    .with_return_type(arena.object([Ty::property(
        "value",
        arena.type_reference("T", std::iter::empty()),
    )]));
    context.add_candidate(
        type_parameter,
        arena.string_literal("ready"),
        InferencePriority::NakedTypeVariable,
        InferenceVariance::Covariant,
    );

    assert_eq!(context.get_inferred_type(0, &checker), Some(Ty::string()));
}

#[test]
fn top_level_literal_candidates_are_preserved_for_top_level_return() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter = Ty::type_parameter("T", None, None);
    let mut context = InferenceContext::with_substitutions(
        [type_parameter],
        &TypeParameterSubstitutions::new(),
        arena,
    )
    .with_return_type(arena.type_reference("T", std::iter::empty()));
    context.add_candidate(
        type_parameter,
        arena.string_literal("ready"),
        InferencePriority::NakedTypeVariable,
        InferenceVariance::Covariant,
    );

    assert_optional_type_eq(
        arena,
        context.get_inferred_type(0, &checker),
        Some(arena.string_literal("ready")),
    );
}

#[test]
fn forward_default_references_resolve_to_unknown() {
    let allocator = Allocator::default();
    test_checker!(allocator, store, checker, arena);
    let type_parameter_t = Ty::type_parameter(
        "T",
        None,
        Some(arena.type_reference("U", std::iter::empty())),
    );
    let type_parameter_u = Ty::type_parameter("U", None, None);
    let mut context = InferenceContext::with_substitutions(
        [type_parameter_t, type_parameter_u],
        &TypeParameterSubstitutions::new(),
        arena,
    );

    assert_eq!(
        context.resolve_type_parameter_by_name("T", &checker, InferenceResolutionFlags::NONE,),
        Some(Ty::unknown()),
    );
    assert!(!context.inferences[1].is_fixed);
}
