use num_traits::ToPrimitive;
use oxc_ast::{
    AstKind,
    ast::{
        ArrowFunctionExpression, CallExpression, Expression, FormalParameters, Function,
        FunctionBody, NewExpression, ReturnStatement, TSSignature, TSTupleElement, TSType,
        TSTypeParameterInstantiation, YieldExpression,
    },
};
use oxc_ast_visit::Visit;
use oxc_cfg::{
    EdgeType, InstructionKind,
    graph::{Direction, visit::EdgeRef},
};
use oxc_semantic::{NodeId, ScopeFlags};
use rustc_hash::FxHashSet;
use std::cell::RefCell;

use crate::{
    checker::Checker,
    checker_impl::{FunctionKind, GetTypeFlags},
    index_type_to_property_name,
    limits::{CONDITIONAL_INFER_MATCH_MAX_DEPTH, CONDITIONAL_TYPE_MAX_DEPTH},
    mapper::{TypeMapper, TypeParameterSubstitutions},
    program::ProgramId,
    types::{
        CheckerArena, MappedModifier, SignatureKind, TupleElement, Ty, TyFunction, TyInfer, TyKind,
        TyMapped, TyProperty, TyTypeParameter, TypeErrorKind,
        function_parameter_type_at_call_index, visit_type,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ConditionalInferMatchResult {
    Matched,
    NoMatch,
    Deferred,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PropertyMatchMode {
    ExistingOnly,
    RequireTarget,
}

impl ConditionalInferMatchResult {
    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::NoMatch, _) | (_, Self::NoMatch) => Self::NoMatch,
            (Self::Deferred, _) | (_, Self::Deferred) => Self::Deferred,
            (Self::Matched, Self::Matched) => Self::Matched,
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum InferencePriority {
    None,
    Low,
    ReturnType,
    MappedTypeConstraint,
    PartialSameShapeMappedType,
    SameShapeMappedType,
    NakedTypeVariable,
}

impl InferencePriority {
    fn structural(self) -> Self {
        match self {
            Self::None => Self::None,
            _ => Self::Low,
        }
    }

    fn return_type(self) -> Self {
        match self {
            Self::None => Self::None,
            _ => Self::ReturnType,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct InferenceResolutionFlags {
    fill_unresolved_with_unknown: bool,
}

impl InferenceResolutionFlags {
    const NONE: Self = Self {
        fill_unresolved_with_unknown: false,
    };

    const FILL_UNRESOLVED_WITH_UNKNOWN: Self = Self {
        fill_unresolved_with_unknown: true,
    };

    fn fill_unresolved_with_unknown(self) -> bool {
        self.fill_unresolved_with_unknown
    }
}

#[derive(Clone, Debug)]
struct InferenceInfo<'a> {
    type_parameter: TyTypeParameter<'a>,
    candidates: Vec<Ty<'a>>,
    contra_candidates: Vec<Ty<'a>>,
    inferred_type: Option<Ty<'a>>,
    priority: InferencePriority,
    top_level: bool,
    is_fixed: bool,
}

impl<'a> InferenceInfo<'a> {
    fn new(type_parameter: TyTypeParameter<'a>, fixed_type: Option<Ty<'a>>) -> Self {
        Self {
            type_parameter,
            candidates: Vec::new(),
            contra_candidates: Vec::new(),
            inferred_type: fixed_type,
            priority: InferencePriority::None,
            top_level: false,
            is_fixed: fixed_type.is_some(),
        }
    }
}

#[derive(Clone)]
struct InferenceContext<'a> {
    arena: CheckerArena<'a>,
    inferences: Vec<InferenceInfo<'a>>,
    return_type: Option<Ty<'a>>,
}

pub(crate) struct InferenceResolution<'a> {
    substitutions: TypeParameterSubstitutions<'a>,
    mapper: TypeMapper<'a>,
}

impl<'a> InferenceResolution<'a> {
    fn new_with_mapper(
        substitutions: TypeParameterSubstitutions<'a>,
        mapper: TypeMapper<'a>,
    ) -> Self {
        Self {
            substitutions,
            mapper,
        }
    }

    pub(crate) fn substitutions(&self) -> &TypeParameterSubstitutions<'a> {
        &self.substitutions
    }

    pub(crate) fn mapper(&self) -> &TypeMapper<'a> {
        &self.mapper
    }
}

impl<'a> InferenceContext<'a> {
    fn with_substitutions(
        type_parameters: impl IntoIterator<Item = TyTypeParameter<'a>>,
        substitutions: &TypeParameterSubstitutions<'a>,
        arena: CheckerArena<'a>,
    ) -> Self {
        Self {
            arena,
            inferences: type_parameters
                .into_iter()
                .map(|type_parameter| {
                    InferenceInfo::new(type_parameter, substitutions.get(type_parameter))
                })
                .collect(),
            return_type: None,
        }
    }

    fn with_return_type(mut self, return_type: Ty<'a>) -> Self {
        self.return_type = Some(return_type);
        self
    }

    fn inference_by_name_mut(&mut self, name: &str) -> Option<&mut InferenceInfo<'a>> {
        self.inferences
            .iter_mut()
            .find(|inference| inference.type_parameter.name == name)
    }

    fn inference_index_by_name(&self, name: &str) -> Option<usize> {
        self.inferences
            .iter()
            .position(|inference| inference.type_parameter.name == name)
    }

    fn type_parameter_by_name(&self, name: &str) -> Option<TyTypeParameter<'a>> {
        self.inferences.iter().find_map(|inference| {
            (inference.type_parameter.name == name).then_some(inference.type_parameter)
        })
    }

    fn inference_for_type_parameter_mut(
        &mut self,
        type_parameter: TyTypeParameter<'a>,
    ) -> Option<&mut InferenceInfo<'a>> {
        self.inferences
            .iter_mut()
            .find(|inference| inference.type_parameter == type_parameter)
    }

    fn contains_type_parameter_name(&self, name: &str) -> bool {
        self.inferences
            .iter()
            .any(|inference| inference.type_parameter.name == name)
    }

    fn add_candidate(
        &mut self,
        type_parameter: TyTypeParameter<'a>,
        candidate: Ty<'a>,
        priority: InferencePriority,
        direction: InferenceVariance,
    ) {
        let arena = self.arena;
        let Some(inference) = self.inference_for_type_parameter_mut(type_parameter) else {
            return;
        };
        if inference.is_fixed {
            return;
        }
        if priority > inference.priority {
            match direction {
                InferenceVariance::Covariant => inference.candidates.clear(),
                InferenceVariance::Contravariant => {
                    inference.candidates.clear();
                    inference.contra_candidates.clear();
                }
            }
            inference.priority = priority;
        } else if priority < inference.priority {
            return;
        }
        inference.top_level |= priority == InferencePriority::NakedTypeVariable;
        let is_duplicate = match direction {
            InferenceVariance::Covariant => inference
                .candidates
                .iter()
                .any(|existing| arena.is_type_identical_to(*existing, candidate)),
            InferenceVariance::Contravariant => inference
                .contra_candidates
                .iter()
                .any(|existing| arena.is_type_identical_to(*existing, candidate)),
        };
        if !is_duplicate {
            match direction {
                InferenceVariance::Covariant => inference.candidates.push(candidate),
                InferenceVariance::Contravariant => inference.contra_candidates.push(candidate),
            }
            inference.inferred_type = None;
        }
    }

    fn resolve_with_contextual_mapper<'store>(
        mut self,
        checker: &Checker<'a, 'store>,
        flags: InferenceResolutionFlags,
    ) -> InferenceResolution<'a> {
        let arena = checker.arena();
        let substitutions = self.resolve_substitutions(checker, flags);
        let contextual_pairs = self
            .inferences
            .iter()
            .map(|inference| {
                let source =
                    Ty::type_reference(arena, inference.type_parameter.name, std::iter::empty());
                let fallback_target = substitutions
                    .get(inference.type_parameter)
                    .unwrap_or(source);
                (source, fallback_target)
            })
            .collect::<Vec<_>>();
        let contextual_context = RefCell::new(self);
        let mapper =
            TypeMapper::from_contextual_inference_pairs(arena, contextual_pairs, move |name| {
                contextual_context
                    .borrow_mut()
                    .resolve_type_parameter_by_name_in_mapper(name)
            });
        InferenceResolution::new_with_mapper(substitutions, mapper)
    }

    fn resolve_type_parameter_by_name_in_mapper(&mut self, name: &str) -> Option<Ty<'a>> {
        let index = self.inference_index_by_name(name)?;
        let inferred_type = self.inferences[index].inferred_type?;
        self.inferences[index].is_fixed = true;
        Some(inferred_type)
    }

    fn resolve_substitutions<'store>(
        &mut self,
        checker: &Checker<'a, 'store>,
        flags: InferenceResolutionFlags,
    ) -> TypeParameterSubstitutions<'a> {
        let mut substitutions = TypeParameterSubstitutions::new();
        for index in 0..self.inferences.len() {
            if let Some(inferred_type) =
                self.resolve_inference_at_index(index, checker, flags, &mut Vec::new(), false)
            {
                substitutions.insert(self.inferences[index].type_parameter, inferred_type);
            }
        }
        substitutions
    }

    #[cfg(test)]
    fn resolve_type_parameter_by_name<'store>(
        &mut self,
        name: &str,
        checker: &Checker<'a, 'store>,
        flags: InferenceResolutionFlags,
    ) -> Option<Ty<'a>> {
        let index = self.inference_index_by_name(name)?;
        self.resolve_inference_at_index(index, checker, flags, &mut Vec::new(), true)
    }

    fn resolve_inference_at_index<'store>(
        &mut self,
        index: usize,
        checker: &Checker<'a, 'store>,
        flags: InferenceResolutionFlags,
        resolving: &mut Vec<usize>,
        fix: bool,
    ) -> Option<Ty<'a>> {
        let arena = checker.arena();
        if let Some(inferred_type) = self.inferences[index].inferred_type {
            if fix {
                self.inferences[index].is_fixed = true;
            }
            return Some(inferred_type);
        }
        if resolving.contains(&index) {
            return None;
        }

        resolving.push(index);
        let mut inferred_type = self.get_inferred_type(index, checker);

        if inferred_type.is_none()
            && let Some(fallback_type) = self.inferences[index]
                .type_parameter
                .default_type
                .or(self.inferences[index].type_parameter.constraint_type)
        {
            for dependency_index in self.fallback_dependency_indices(arena, fallback_type) {
                if dependency_index < index {
                    self.resolve_inference_at_index(
                        dependency_index,
                        checker,
                        flags,
                        resolving,
                        true,
                    );
                }
            }
            let substitutions = self.fallback_substitutions(arena, index, fallback_type);
            let fallback_type =
                checker.instantiate_type(fallback_type, &substitutions.to_mapper(arena));
            self.inferences[index].inferred_type = Some(fallback_type);
            inferred_type = Some(fallback_type);
        }

        if let Some(current_inferred_type) = inferred_type
            && let Some(constraint_type) = self.inferences[index].type_parameter.constraint_type
        {
            for dependency_index in self.fallback_dependency_indices(arena, constraint_type) {
                if dependency_index != index {
                    self.resolve_inference_at_index(
                        dependency_index,
                        checker,
                        flags,
                        resolving,
                        false,
                    );
                }
            }
            let substitutions = self.resolved_substitutions();
            let constraint_type =
                checker.instantiate_type(constraint_type, &substitutions.to_mapper(arena));
            if !checker.is_assignable_to(current_inferred_type, constraint_type) {
                self.inferences[index].inferred_type = Some(constraint_type);
                inferred_type = Some(constraint_type);
            }
        }

        if inferred_type.is_none() && flags.fill_unresolved_with_unknown() {
            self.inferences[index].inferred_type = Some(Ty::unknown());
            inferred_type = Some(Ty::unknown());
        }

        if fix && inferred_type.is_some() {
            self.inferences[index].is_fixed = true;
        }
        resolving.pop();
        inferred_type
    }

    fn resolved_substitutions(&self) -> TypeParameterSubstitutions<'a> {
        let mut substitutions = TypeParameterSubstitutions::new();
        for inference in &self.inferences {
            if let Some(inferred_type) = inference.inferred_type {
                substitutions.insert(inference.type_parameter, inferred_type);
            }
        }
        substitutions
    }

    fn fallback_substitutions(
        &self,
        arena: CheckerArena<'a>,
        current_index: usize,
        fallback_type: Ty<'a>,
    ) -> TypeParameterSubstitutions<'a> {
        let mut substitutions = self.resolved_substitutions();
        for dependency_index in self.fallback_dependency_indices(arena, fallback_type) {
            if dependency_index >= current_index
                && self.inferences[dependency_index].inferred_type.is_none()
            {
                substitutions.insert(
                    self.inferences[dependency_index].type_parameter,
                    Ty::unknown(),
                );
            }
        }
        substitutions
    }

    fn fallback_dependency_indices(
        &self,
        arena: CheckerArena<'a>,
        fallback_type: Ty<'a>,
    ) -> Vec<usize> {
        let mut indices = Vec::new();
        visit_type(arena, fallback_type, &mut |ty| {
            let TyKind::TypeReference(reference) = arena.ty_kind(ty) else {
                return;
            };
            if !reference.is_bare() {
                return;
            }
            let Some(index) = self.inference_index_by_name(reference.name) else {
                return;
            };
            if !indices.contains(&index) {
                indices.push(index);
            }
        });
        indices
    }

    fn candidate_substitutions<'store>(
        &mut self,
        checker: &Checker<'a, 'store>,
    ) -> TypeParameterSubstitutions<'a> {
        let mut substitutions = TypeParameterSubstitutions::new();
        for index in 0..self.inferences.len() {
            if let Some(inferred_type) = self.get_inferred_type(index, checker) {
                substitutions.insert(self.inferences[index].type_parameter, inferred_type);
            }
        }
        substitutions
    }

    fn get_inferred_type<'store>(
        &mut self,
        index: usize,
        checker: &Checker<'a, 'store>,
    ) -> Option<Ty<'a>> {
        if self.inferences[index].inferred_type.is_none() {
            let inference = &self.inferences[index];
            self.inferences[index].inferred_type =
                inferred_type_from_candidates(checker, inference, self.return_type);
        }
        self.inferences[index].inferred_type
    }
}

fn inferred_type_from_candidates<'a, 'store>(
    checker: &Checker<'a, 'store>,
    inference: &InferenceInfo<'a>,
    return_type: Option<Ty<'a>>,
) -> Option<Ty<'a>> {
    let arena = checker.arena();
    let covariant = resolve_covariant_candidates(checker, inference, return_type);
    let contravariant = resolve_contravariant_candidates(checker, inference);

    match (covariant, contravariant) {
        (Some(covariant), Some(contravariant)) => {
            if covariant.is_never() || covariant.is_any_like(arena) {
                return Some(contravariant);
            }
            if inference
                .contra_candidates
                .iter()
                .any(|candidate| checker.is_assignable_to(covariant, *candidate))
            {
                Some(covariant)
            } else {
                Some(contravariant)
            }
        }
        (Some(covariant), None) => Some(covariant),
        (None, Some(contravariant)) => Some(contravariant),
        (None, None) => None,
    }
}

fn resolve_covariant_candidates<'a, 'store>(
    checker: &Checker<'a, 'store>,
    inference: &InferenceInfo<'a>,
    return_type: Option<Ty<'a>>,
) -> Option<Ty<'a>> {
    let arena = checker.arena();
    if inference.candidates.is_empty() {
        return None;
    }

    if return_type.is_none() {
        return Some(Ty::union(arena, inference.candidates.iter().copied()));
    }

    let candidates = if should_widen_literal_inference(arena, inference, return_type) {
        inference
            .candidates
            .iter()
            .map(|candidate| get_widened_literal_type(arena, *candidate))
            .collect::<Vec<_>>()
    } else {
        inference.candidates.clone()
    };

    if inference_priority_implies_combination(inference.priority) {
        Some(Ty::union(arena, candidates))
    } else {
        Some(get_common_supertype(checker, &candidates))
    }
}

fn resolve_contravariant_candidates<'a, 'store>(
    checker: &Checker<'a, 'store>,
    inference: &InferenceInfo<'a>,
) -> Option<Ty<'a>> {
    let arena = checker.arena();
    if inference.contra_candidates.is_empty() {
        return None;
    }

    if inference_priority_implies_combination(inference.priority) {
        Some(Ty::intersection(
            arena,
            inference.contra_candidates.iter().copied(),
        ))
    } else {
        Some(get_common_subtype(checker, &inference.contra_candidates))
    }
}

fn inference_priority_implies_combination(priority: InferencePriority) -> bool {
    matches!(
        priority,
        InferencePriority::MappedTypeConstraint
            | InferencePriority::PartialSameShapeMappedType
            | InferencePriority::SameShapeMappedType
    )
}

fn should_widen_literal_inference<'a>(
    arena: CheckerArena<'a>,
    inference: &InferenceInfo<'a>,
    return_type: Option<Ty<'a>>,
) -> bool {
    !has_primitive_constraint(arena, inference.type_parameter)
        && inference.top_level
        && return_type.is_some_and(|return_type| {
            !is_type_parameter_at_top_level(arena, return_type, inference.type_parameter, 0)
        })
}

fn has_primitive_constraint<'a>(
    arena: CheckerArena<'a>,
    type_parameter: TyTypeParameter<'a>,
) -> bool {
    type_parameter
        .constraint_type
        .is_some_and(|ty| type_maybe_contains_primitive_or_literal(arena, ty))
}

fn type_maybe_contains_primitive_or_literal<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> bool {
    match arena.ty_kind(ty) {
        TyKind::String
        | TyKind::Number
        | TyKind::Bigint
        | TyKind::Boolean
        | TyKind::Symbol
        | TyKind::StringLiteral(_)
        | TyKind::NumberLiteral(_)
        | TyKind::BigIntLiteral(_)
        | TyKind::BooleanLiteral(_)
        | TyKind::UniqueSymbol(_)
        | TyKind::Keyof(_)
        | TyKind::TemplateLiteral(_) => true,
        TyKind::Union(union) => union
            .types
            .iter()
            .any(|ty| type_maybe_contains_primitive_or_literal(arena, *ty)),
        TyKind::Intersection(intersection) => intersection
            .types
            .iter()
            .any(|ty| type_maybe_contains_primitive_or_literal(arena, *ty)),
        TyKind::Conditional(conditional) => {
            type_maybe_contains_primitive_or_literal(arena, conditional.true_type)
                || type_maybe_contains_primitive_or_literal(arena, conditional.false_type)
        }
        _ => false,
    }
}

fn is_type_parameter_at_top_level<'a>(
    arena: CheckerArena<'a>,
    ty: Ty<'a>,
    type_parameter: TyTypeParameter<'a>,
    depth: usize,
) -> bool {
    match arena.ty_kind(ty) {
        TyKind::TypeReference(reference) => {
            reference.is_bare() && reference.name == type_parameter.name
        }
        TyKind::Union(union) => union
            .types
            .iter()
            .any(|ty| is_type_parameter_at_top_level(arena, *ty, type_parameter, depth)),
        TyKind::Intersection(intersection) => intersection
            .types
            .iter()
            .any(|ty| is_type_parameter_at_top_level(arena, *ty, type_parameter, depth)),
        TyKind::Conditional(conditional) if depth < 3 => {
            is_type_parameter_at_top_level(arena, conditional.true_type, type_parameter, depth + 1)
                || is_type_parameter_at_top_level(
                    arena,
                    conditional.false_type,
                    type_parameter,
                    depth + 1,
                )
        }
        _ => false,
    }
}

fn get_widened_literal_type<'a>(arena: crate::types::CheckerArena<'a>, ty: Ty<'a>) -> Ty<'a> {
    match arena.ty_kind(ty) {
        TyKind::StringLiteral(_) | TyKind::TemplateLiteral(_) => Ty::string(),
        TyKind::NumberLiteral(_) => Ty::number(),
        TyKind::BigIntLiteral(_) => Ty::bigint(),
        TyKind::BooleanLiteral(_) => Ty::boolean(),
        TyKind::Union(union) => Ty::union(
            arena,
            union
                .types
                .iter()
                .map(|ty| get_widened_literal_type(arena, *ty)),
        ),
        _ => ty,
    }
}

fn get_common_supertype<'a, 'store>(
    checker: &Checker<'a, 'store>,
    candidates: &[Ty<'a>],
) -> Ty<'a> {
    let arena = checker.arena();
    if candidates.len() == 1 {
        return candidates[0];
    }
    if literal_types_with_same_base_type(arena, candidates) {
        return Ty::union(arena, candidates.iter().copied());
    }

    find_leftmost_type(checker, candidates)
}

fn get_common_subtype<'a, 'store>(checker: &Checker<'a, 'store>, candidates: &[Ty<'a>]) -> Ty<'a> {
    let mut subtype = candidates[0];
    for candidate in candidates.iter().skip(1) {
        if checker.is_assignable_to(*candidate, subtype) {
            subtype = *candidate;
        }
    }
    subtype
}

fn find_leftmost_type<'a, 'store>(checker: &Checker<'a, 'store>, candidates: &[Ty<'a>]) -> Ty<'a> {
    let mut candidate = candidates[0];
    for ty in candidates.iter().skip(1) {
        if checker.is_assignable_to(candidate, *ty) {
            candidate = *ty;
        }
    }
    candidate
}

fn literal_types_with_same_base_type<'a>(arena: CheckerArena<'a>, candidates: &[Ty<'a>]) -> bool {
    let Some(common_base) = candidates
        .first()
        .and_then(|candidate| literal_base_type(arena, *candidate))
    else {
        return candidates.is_empty();
    };
    candidates
        .iter()
        .skip(1)
        .all(|candidate| literal_base_type(arena, *candidate) == Some(common_base))
}

fn literal_base_type<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> Option<Ty<'static>> {
    match arena.ty_kind(ty) {
        TyKind::StringLiteral(_) => Some(Ty::String),
        TyKind::NumberLiteral(_) => Some(Ty::Number),
        TyKind::BigIntLiteral(_) => Some(Ty::Bigint),
        TyKind::BooleanLiteral(_) => Some(Ty::Boolean),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InferenceVariance {
    Covariant,
    Contravariant,
}

impl InferenceVariance {
    fn flip(self) -> Self {
        match self {
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
        }
    }
}

impl<'a, 'store> Checker<'a, 'store> {
    pub(crate) fn infer_type_parameter_names(&self, ty: Ty<'a>) -> Vec<&'a str> {
        let mut names = Vec::new();
        self.collect_infer_type_parameter_names(ty, &mut names);
        names
    }

    pub(crate) fn contains_infer_type_parameter(&self, ty: Ty<'a>) -> bool {
        let mut contains = false;
        visit_type(self.arena(), ty, &mut |ty| {
            contains |= matches!(self.ty_kind(ty), TyKind::Infer(_));
        });
        contains
    }

    fn collect_infer_type_parameter_names(&self, ty: Ty<'a>, names: &mut Vec<&'a str>) {
        visit_type(self.arena(), ty, &mut |ty| {
            if let TyKind::Infer(infer) = self.ty_kind(ty)
                && !names.contains(&infer.type_parameter.name)
            {
                names.push(infer.type_parameter.name);
            }
        });
    }

    pub(crate) fn conditional_type(
        &self,
        check_type: Ty<'a>,
        extends_type: Ty<'a>,
        true_type: Ty<'a>,
        false_type: Ty<'a>,
        is_distributive: bool,
    ) -> Ty<'a> {
        let depth = &self.conditional_type_depth;
        let current = depth.get();
        if current >= CONDITIONAL_TYPE_MAX_DEPTH {
            if !self.resolving_type_aliases.borrow().is_empty() {
                self.mark_type_instantiation_overflow();
                return Ty::error(self.arena(), TypeErrorKind::ConditionalTypeDepthExceeded);
            }
            return Ty::conditional(
                self.arena(),
                check_type,
                extends_type,
                true_type,
                false_type,
                is_distributive,
            );
        }

        depth.set(current + 1);
        let result = self.conditional_type_inner(
            check_type,
            extends_type,
            true_type,
            false_type,
            is_distributive,
        );
        depth.set(current);
        result
    }

    fn conditional_type_inner(
        &self,
        check_type: Ty<'a>,
        extends_type: Ty<'a>,
        true_type: Ty<'a>,
        false_type: Ty<'a>,
        is_distributive: bool,
    ) -> Ty<'a> {
        if let Some(is_equal) =
            self.simplify_type_equality_function_extends(check_type, extends_type)
        {
            return if is_equal { true_type } else { false_type };
        }

        if self.contains_infer_type_parameter(check_type)
            || self.contains_infer_type_parameter(extends_type)
        {
            let mut inferences = self.conditional_inference_context(check_type, extends_type);
            let inference_result =
                self.infer_conditional_from_types(check_type, extends_type, &mut inferences, 0);
            return match inference_result {
                ConditionalInferMatchResult::Matched => {
                    let resolution = inferences
                        .resolve_with_contextual_mapper(self, InferenceResolutionFlags::NONE);
                    self.instantiate_type(true_type, resolution.mapper())
                }
                ConditionalInferMatchResult::NoMatch => false_type,
                ConditionalInferMatchResult::Deferred => Ty::conditional(
                    self.arena(),
                    check_type,
                    extends_type,
                    true_type,
                    false_type,
                    is_distributive,
                ),
            };
        }

        if !self.could_contain_type_variables(check_type)
            && !self.could_contain_type_variables(extends_type)
        {
            return if self.is_assignable_to(check_type, extends_type) {
                true_type
            } else {
                false_type
            };
        }

        Ty::conditional(
            self.arena(),
            check_type,
            extends_type,
            true_type,
            false_type,
            is_distributive,
        )
    }

    fn simplify_type_equality_function_extends(
        &self,
        check_type: Ty<'a>,
        extends_type: Ty<'a>,
    ) -> Option<bool> {
        let (TyKind::Function(check_function), TyKind::Function(extends_function)) =
            (self.ty_kind(check_type), self.ty_kind(extends_type))
        else {
            return None;
        };
        if !check_function.parameters.is_empty()
            || !extends_function.parameters.is_empty()
            || check_function.type_parameters.len() != 1
            || extends_function.type_parameters.len() != 1
        {
            return None;
        }

        let TyKind::Conditional(check_return) = self.ty_kind(check_function.return_type) else {
            return None;
        };
        let TyKind::Conditional(extends_return) = self.ty_kind(extends_function.return_type) else {
            return None;
        };
        if self.could_contain_type_variables(check_return.extends_type)
            || self.could_contain_type_variables(extends_return.extends_type)
            || self.contains_infer_type_parameter(check_return.extends_type)
            || self.contains_infer_type_parameter(extends_return.extends_type)
        {
            return None;
        }

        Some(
            self.is_assignable_to(check_return.extends_type, extends_return.extends_type)
                && self.is_assignable_to(extends_return.extends_type, check_return.extends_type),
        )
    }

    fn conditional_inference_context(
        &self,
        check_type: Ty<'a>,
        extends_type: Ty<'a>,
    ) -> InferenceContext<'a> {
        let mut type_parameters = Vec::new();
        for ty in [check_type, extends_type] {
            self.collect_infer_types(ty, &mut |infer| {
                if !type_parameters
                    .iter()
                    .any(|type_parameter: &TyTypeParameter<'a>| {
                        type_parameter.name == infer.type_parameter.name
                    })
                {
                    type_parameters.push(infer.type_parameter);
                }
            });
        }
        InferenceContext::with_substitutions(
            type_parameters,
            &TypeParameterSubstitutions::new(),
            self.arena(),
        )
    }

    fn add_conditional_inference(
        &self,
        inferences: &mut InferenceContext<'a>,
        infer: &TyInfer<'a>,
        candidate: Ty<'a>,
    ) -> ConditionalInferMatchResult {
        if let Some(constraint_type) = infer.type_parameter.constraint_type {
            let substitutions = inferences.candidate_substitutions(self);
            let constraint_type =
                self.instantiate_type(constraint_type, &substitutions.to_mapper(self.arena()));
            if self.contains_infer_type_parameter(constraint_type)
                || self.could_contain_type_variables(constraint_type)
            {
                return ConditionalInferMatchResult::Deferred;
            }
            if !self.is_assignable_to(candidate, constraint_type) {
                return ConditionalInferMatchResult::NoMatch;
            }
        }

        inferences.add_candidate(
            infer.type_parameter,
            candidate,
            InferencePriority::NakedTypeVariable,
            InferenceVariance::Covariant,
        );
        ConditionalInferMatchResult::Matched
    }

    fn infer_conditional_from_types(
        &self,
        source: Ty<'a>,
        target: Ty<'a>,
        inferences: &mut InferenceContext<'a>,
        depth: usize,
    ) -> ConditionalInferMatchResult {
        if depth >= CONDITIONAL_INFER_MATCH_MAX_DEPTH {
            return ConditionalInferMatchResult::Deferred;
        }
        if self.arena().is_type_identical_to(source, target)
            && !self.contains_infer_type_parameter(target)
        {
            return ConditionalInferMatchResult::Matched;
        }

        match (self.ty_kind(source), self.ty_kind(target)) {
            (_, TyKind::Infer(infer)) => self.add_conditional_inference(inferences, infer, source),
            (TyKind::Any | TyKind::Error(_), _) if self.contains_infer_type_parameter(target) => {
                let mut result = ConditionalInferMatchResult::Matched;
                self.collect_infer_types(target, &mut |infer| {
                    result = result.and(self.add_conditional_inference(inferences, infer, source));
                });
                result
            }
            (TyKind::Object(source), TyKind::Object(target)) => self
                .infer_conditional_from_properties(
                    source.properties.iter().copied(),
                    target.properties.iter().copied(),
                    inferences,
                    depth + 1,
                ),
            (TyKind::Object(source), TyKind::Function(target)) => source
                .signatures()
                .iter()
                .rev()
                .find(|signature| signature.kind == SignatureKind::Call)
                .map(|signature| {
                    self.infer_conditional_from_function_types(
                        signature.function(self.arena()),
                        target,
                        inferences,
                        depth + 1,
                    )
                })
                .unwrap_or(ConditionalInferMatchResult::NoMatch),
            (TyKind::Array(source), TyKind::Array(target)) => self.infer_conditional_from_types(
                source.element_type,
                target.element_type,
                inferences,
                depth + 1,
            ),
            (TyKind::Tuple(source), TyKind::Tuple(target)) => self
                .infer_conditional_from_tuple_elements(
                    &source.elements,
                    &target.elements,
                    inferences,
                    depth + 1,
                ),
            (TyKind::Function(source), TyKind::Function(target)) => {
                self.infer_conditional_from_function_types(source, target, inferences, depth + 1)
            }
            (TyKind::IndexedAccess(source), TyKind::IndexedAccess(target)) => self
                .infer_conditional_from_type_pairs(
                    [
                        (source.object_type, target.object_type),
                        (source.index_type, target.index_type),
                    ],
                    inferences,
                    depth + 1,
                ),
            (TyKind::TypeReference(source), TyKind::TypeReference(target))
                if source.has_identical_target(target)
                    && source.type_arguments.len() == target.type_arguments.len() =>
            {
                self.infer_conditional_from_type_pairs(
                    source
                        .type_arguments
                        .iter()
                        .copied()
                        .zip(target.type_arguments.iter().copied()),
                    inferences,
                    depth + 1,
                )
            }
            (TyKind::Union(source), TyKind::Union(target))
                if source.types.len() == target.types.len() =>
            {
                self.infer_conditional_from_type_pairs(
                    source
                        .types
                        .iter()
                        .copied()
                        .zip(target.types.iter().copied()),
                    inferences,
                    depth + 1,
                )
            }
            (TyKind::Union(source_union), _) => {
                let mut result = ConditionalInferMatchResult::Matched;
                for source_type in &source_union.types {
                    result = result.and(self.infer_conditional_from_types(
                        *source_type,
                        target,
                        inferences,
                        depth + 1,
                    ));
                    if result == ConditionalInferMatchResult::NoMatch {
                        return result;
                    }
                }
                result
            }
            (_, TyKind::Union(target_union)) => {
                let mut deferred = false;
                for target_type in &target_union.types {
                    let mut branch_inferences = inferences.clone();
                    match self.infer_conditional_from_types(
                        source,
                        *target_type,
                        &mut branch_inferences,
                        depth + 1,
                    ) {
                        ConditionalInferMatchResult::Matched => {
                            *inferences = branch_inferences;
                            return ConditionalInferMatchResult::Matched;
                        }
                        ConditionalInferMatchResult::Deferred => deferred = true,
                        ConditionalInferMatchResult::NoMatch => {}
                    }
                }
                if deferred {
                    ConditionalInferMatchResult::Deferred
                } else {
                    ConditionalInferMatchResult::NoMatch
                }
            }
            (_, TyKind::Intersection(target_intersection)) => {
                // An intersection constraint is conjunctive. Match every constituent so a
                // definite failure can select the false branch and successful constituents
                // can contribute `infer` candidates to the true branch.
                self.infer_conditional_from_type_pairs(
                    target_intersection
                        .types
                        .iter()
                        .map(|target| (source, *target)),
                    inferences,
                    depth + 1,
                )
            }
            _ => {
                if self.is_active_unresolved_type_alias(source) {
                    ConditionalInferMatchResult::Deferred
                } else if self.is_assignable_to(source, target) {
                    ConditionalInferMatchResult::Matched
                } else if self.could_contain_type_variables(source)
                    || matches!(
                        self.ty_kind(source),
                        TyKind::TypeReference(_) | TyKind::TypeQuery(_)
                    )
                    || (self.could_contain_type_variables(target)
                        && !matches!(
                            self.ty_kind(target),
                            TyKind::Object(_)
                                | TyKind::Function(_)
                                | TyKind::Array(_)
                                | TyKind::Tuple(_)
                                | TyKind::PrimitiveObject
                        ))
                {
                    ConditionalInferMatchResult::Deferred
                } else {
                    ConditionalInferMatchResult::NoMatch
                }
            }
        }
    }

    fn infer_conditional_from_properties(
        &self,
        source_properties: impl IntoIterator<Item = TyProperty<'a>>,
        target_properties: impl IntoIterator<Item = TyProperty<'a>>,
        inferences: &mut InferenceContext<'a>,
        depth: usize,
    ) -> ConditionalInferMatchResult {
        match_property_type_pairs(
            source_properties,
            target_properties,
            PropertyMatchMode::RequireTarget,
        )
        .map(|pairs| self.infer_conditional_from_type_pairs(pairs, inferences, depth + 1))
        .unwrap_or(ConditionalInferMatchResult::NoMatch)
    }

    fn infer_conditional_from_function_types(
        &self,
        source: &TyFunction<'a>,
        target: &TyFunction<'a>,
        inferences: &mut InferenceContext<'a>,
        depth: usize,
    ) -> ConditionalInferMatchResult {
        let target_rest_index = target
            .parameters
            .iter()
            .position(|parameter| parameter.rest);
        if target_rest_index.is_none() && source.parameters.len() != target.parameters.len() {
            return ConditionalInferMatchResult::NoMatch;
        }
        if let Some(rest_index) = target_rest_index
            && (rest_index + 1 != target.parameters.len() || source.parameters.len() < rest_index)
        {
            return ConditionalInferMatchResult::NoMatch;
        }

        let source_mapper =
            self.infer_conditional_source_function_type_parameter_mapper(source, target);
        let parameter_count = target_rest_index.unwrap_or(target.parameters.len());

        let parameter_pairs = source
            .parameters
            .iter()
            .take(parameter_count)
            .zip(target.parameters.iter())
            .map(|(source, target)| (self.instantiate_type(source.ty, &source_mapper), target.ty));
        self.infer_conditional_from_type_pairs(
            parameter_pairs.chain(std::iter::once((
                self.instantiate_type(source.return_type, &source_mapper),
                target.return_type,
            ))),
            inferences,
            depth + 1,
        )
    }

    fn infer_conditional_source_function_type_parameter_mapper(
        &self,
        source: &TyFunction<'a>,
        target: &TyFunction<'a>,
    ) -> TypeMapper<'a> {
        if source.type_parameters.is_empty() || !target.type_parameters.is_empty() {
            return TypeMapper::Empty;
        }

        TypeMapper::from_type_parameters_and_arguments(
            self.arena(),
            source.type_parameters.iter().copied(),
            source.type_parameters.iter().map(|_| Ty::unknown()),
        )
    }

    fn infer_conditional_from_tuple_elements(
        &self,
        source_elements: &oxc_allocator::Vec<'a, TupleElement<'a>>,
        target_elements: &oxc_allocator::Vec<'a, TupleElement<'a>>,
        inferences: &mut InferenceContext<'a>,
        depth: usize,
    ) -> ConditionalInferMatchResult {
        if let Some((rest_index, TupleElement::Rest(rest_type))) = target_elements
            .iter()
            .enumerate()
            .find(|(_, element)| matches!(element, TupleElement::Rest(_)))
        {
            if rest_index + 1 != target_elements.len() || source_elements.len() < rest_index {
                return ConditionalInferMatchResult::Deferred;
            }
            let mut result = self.infer_conditional_from_tuple_elements(
                &self
                    .arena()
                    .vec_from_iter(source_elements.iter().take(rest_index).copied()),
                &self
                    .arena()
                    .vec_from_iter(target_elements.iter().take(rest_index).copied()),
                inferences,
                depth + 1,
            );
            let rest_tuple = Ty::tuple(
                self.arena(),
                source_elements
                    .iter()
                    .skip(rest_index)
                    .copied()
                    .collect::<Vec<_>>(),
            );
            result = result.and(self.infer_conditional_from_types(
                rest_tuple,
                *rest_type,
                inferences,
                depth + 1,
            ));
            return result;
        }
        if source_elements.len() != target_elements.len() {
            return ConditionalInferMatchResult::NoMatch;
        }
        self.infer_conditional_from_type_pairs(
            source_elements
                .iter()
                .zip(target_elements.iter())
                .map(|(source, target)| (source.ty(), target.ty())),
            inferences,
            depth + 1,
        )
    }

    fn infer_conditional_from_type_pairs(
        &self,
        pairs: impl IntoIterator<Item = (Ty<'a>, Ty<'a>)>,
        inferences: &mut InferenceContext<'a>,
        depth: usize,
    ) -> ConditionalInferMatchResult {
        pairs.into_iter().fold(
            ConditionalInferMatchResult::Matched,
            |result, (source, target)| {
                result.and(self.infer_conditional_from_types(source, target, inferences, depth + 1))
            },
        )
    }

    fn collect_infer_types(&self, ty: Ty<'a>, f: &mut impl FnMut(&TyInfer<'a>)) {
        visit_type(self.arena(), ty, &mut |ty| {
            if let TyKind::Infer(infer) = self.ty_kind(ty) {
                f(infer);
            }
        });
    }

    pub(crate) fn infer_call_type_parameter_resolution(
        &self,
        program_id: ProgramId,
        function: &'a TyFunction<'a>,
        call_expression: &'a CallExpression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> InferenceResolution<'a> {
        let argument_types = call_expression
            .arguments
            .iter()
            .enumerate()
            .filter_map(|(index, argument)| {
                let argument = argument.as_expression()?;
                let parameter_type =
                    function_parameter_type_at_call_index(self.arena(), function, index)?;
                let flags = flags
                    | if self.could_contain_type_variables(parameter_type) {
                        GetTypeFlags::PRESERVE_LITERALS
                    } else {
                        GetTypeFlags::NONE
                    };
                let contextual_type =
                    self.inference_contextual_parameter_type(function, parameter_type);
                let argument_type = self.get_type_of_call_argument_for_parameter(
                    program_id,
                    argument,
                    node_id,
                    contextual_type,
                    flags,
                );
                Some((index, argument_type))
            })
            .collect::<Vec<_>>();

        self.infer_call_type_parameter_resolution_from_argument_types(
            program_id,
            function,
            call_expression.type_arguments.as_deref(),
            argument_types,
        )
    }

    pub(crate) fn infer_call_type_parameter_resolution_from_argument_types(
        &self,
        program_id: ProgramId,
        function: &'a TyFunction<'a>,
        type_arguments: Option<&'a TSTypeParameterInstantiation<'a>>,
        argument_types: impl IntoIterator<Item = (usize, Ty<'a>)>,
    ) -> InferenceResolution<'a> {
        let type_pairs = argument_types
            .into_iter()
            .filter_map(|(index, argument_type)| {
                function_parameter_type_at_call_index(self.arena(), function, index)
                    .map(|parameter_type| (parameter_type, argument_type))
            });
        self.infer_type_parameter_resolution_from_type_pairs(
            program_id,
            function,
            type_arguments,
            type_pairs,
            InferenceResolutionFlags::NONE,
        )
    }

    fn infer_type_parameter_resolution_from_type_pairs(
        &self,
        program_id: ProgramId,
        function: &'a TyFunction<'a>,
        type_arguments: Option<&'a TSTypeParameterInstantiation<'a>>,
        type_pairs: impl IntoIterator<Item = (Ty<'a>, Ty<'a>)>,
        flags: InferenceResolutionFlags,
    ) -> InferenceResolution<'a> {
        let (substitutions, _) =
            self.explicit_type_parameter_substitutions(program_id, function, type_arguments);
        let mut context = InferenceContext::with_substitutions(
            function.type_parameters.iter().copied(),
            &substitutions,
            self.arena(),
        )
        .with_return_type(
            self.inference_return_type_for_literal_widening(program_id, function.return_type),
        );
        for (parameter_type, argument_type) in type_pairs {
            let argument_type =
                self.get_inference_argument_type(program_id, parameter_type, argument_type);
            self.infer_types(parameter_type, argument_type, &mut context);
        }

        context.resolve_with_contextual_mapper(self, flags)
    }

    pub(crate) fn infer_function_return_type(
        &self,
        program_id: ProgramId,
        function: FunctionKind<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let return_type = if let FunctionKind::ArrowFunction(arrow_function) = function
            && let Some(expression) = arrow_function.get_expression()
        {
            self.get_type_of_expression_with_node(
                program_id,
                expression,
                node_id,
                GetTypeFlags::NONE,
            )
        } else {
            let body = match function {
                FunctionKind::Function(f) => f.body.as_deref(),
                FunctionKind::ArrowFunction(f) => Some(f.body.as_ref()),
            };
            let Some(body) = body else {
                return Ty::error(self.arena(), TypeErrorKind::MissingFunctionBody);
            };
            let expressions = ReturnExpressionVisitor::expressions_in_body(body);
            let has_implicit_return = matches!(function, FunctionKind::Function(function) if function.generator)
                && node_id.is_some_and(|node_id| {
                    self.function_has_implicit_return(program_id, function, node_id)
                });

            let return_type = if expressions.return_expressions.is_empty() {
                Ty::void()
            } else {
                let flags = if expressions.return_expressions.len() > 1 || has_implicit_return {
                    GetTypeFlags::PRESERVE_LITERALS
                } else {
                    GetTypeFlags::NONE
                };
                Ty::union(
                    self.arena(),
                    expressions
                        .return_expressions
                        .into_iter()
                        .map(|argument| {
                            self.get_type_of_expression_with_node(
                                program_id, argument, node_id, flags,
                            )
                        })
                        .chain(has_implicit_return.then_some(Ty::undefined())),
                )
            };

            let yield_type = if expressions.yield_expressions.is_empty() {
                Ty::never()
            } else {
                let flags = if expressions.yield_expressions.len() > 1 {
                    GetTypeFlags::PRESERVE_LITERALS
                } else {
                    GetTypeFlags::NONE
                };
                Ty::union(
                    self.arena(),
                    expressions.yield_expressions.into_iter().map(|argument| {
                        self.get_type_of_expression_with_node(program_id, argument, node_id, flags)
                    }),
                )
            };

            if let FunctionKind::Function(f) = function
                && f.generator
            {
                // TODO(completeness): Implement next type inference
                let next_type = Ty::unknown();

                // function*: look for yield expressions and return expressions
                if f.r#async {
                    self.get_global_async_generator_type(
                        program_id,
                        yield_type,
                        return_type,
                        next_type,
                    )
                } else {
                    self.get_global_generator_type(program_id, yield_type, return_type, next_type)
                }
            } else {
                // non-generator function: look at return expressions
                return_type
            }
        };

        if function.returns_promise() {
            self.get_async_function_return_type(program_id, return_type)
        } else {
            return_type
        }
    }

    fn function_has_implicit_return(
        &self,
        program_id: ProgramId,
        function: FunctionKind<'a>,
        node_id: NodeId,
    ) -> bool {
        let nodes = self.nodes(program_id);
        let Some(function_node_id) = std::iter::once(node_id)
            .chain(nodes.ancestor_ids(node_id))
            .find(|candidate_id| match (function, nodes.kind(*candidate_id)) {
                (FunctionKind::Function(function), AstKind::Function(candidate)) => {
                    std::ptr::eq(function, candidate)
                }
                (
                    FunctionKind::ArrowFunction(function),
                    AstKind::ArrowFunctionExpression(candidate),
                ) => std::ptr::eq(function, candidate),
                _ => false,
            })
        else {
            return false;
        };

        let function_block = nodes.cfg_id(function_node_id);
        let Some(cfg) = self.semantic(program_id).cfg() else {
            return false;
        };

        let mut pending = vec![function_block];
        let mut visited = FxHashSet::default();
        while let Some(block_id) = pending.pop() {
            if !visited.insert(block_id) {
                continue;
            }
            if cfg
                .basic_block(block_id)
                .instructions()
                .iter()
                .any(|instruction| matches!(instruction.kind, InstructionKind::ImplicitReturn))
            {
                return true;
            }
            pending.extend(
                cfg.graph
                    .edges_directed(block_id, Direction::Outgoing)
                    .filter(|edge| {
                        !matches!(edge.weight(), EdgeType::NewFunction | EdgeType::Unreachable)
                    })
                    .map(|edge| edge.target()),
            );
        }
        false
    }

    pub(crate) fn infer_construct_type_parameter_resolution(
        &self,
        program_id: ProgramId,
        function: &'a TyFunction<'a>,
        new_expression: &'a NewExpression<'a>,
    ) -> InferenceResolution<'a> {
        let type_pairs = new_expression
            .arguments
            .iter()
            .zip(function.parameters.iter())
            .filter_map(|(argument, parameter)| {
                let argument = argument.as_expression()?;
                let flags = if self.could_contain_type_variables(parameter.ty) {
                    GetTypeFlags::PRESERVE_LITERALS
                } else {
                    GetTypeFlags::NONE
                };
                let contextual_type =
                    self.inference_contextual_parameter_type(function, parameter.ty);
                let argument_type = self.get_type_of_call_argument_for_parameter(
                    program_id,
                    argument,
                    None,
                    contextual_type,
                    flags,
                );
                Some((parameter.ty, argument_type))
            });
        self.infer_type_parameter_resolution_from_type_pairs(
            program_id,
            function,
            new_expression.type_arguments.as_deref(),
            type_pairs,
            InferenceResolutionFlags::FILL_UNRESOLVED_WITH_UNKNOWN,
        )
    }

    pub(crate) fn inference_contextual_parameter_type(
        &self,
        function: &TyFunction<'a>,
        parameter_type: Ty<'a>,
    ) -> Ty<'a> {
        let TyKind::TypeReference(reference) = self.ty_kind(parameter_type) else {
            return parameter_type;
        };
        if !reference.is_bare() {
            return parameter_type;
        }

        function
            .type_parameters
            .iter()
            .find(|type_parameter| type_parameter.name == reference.name)
            .and_then(|type_parameter| type_parameter.constraint_type)
            .unwrap_or(parameter_type)
    }

    fn inference_return_type_for_literal_widening(
        &self,
        program_id: ProgramId,
        return_type: Ty<'a>,
    ) -> Ty<'a> {
        match self.ty_kind(return_type) {
            TyKind::TypeReference(_)
                if self.is_empty_object_intersection_alias_reference(program_id, return_type) =>
            {
                self.get_expanded_type_alias_reference_type(program_id, return_type, 0)
                    .map(|(expanded_program_id, expanded)| {
                        self.inference_return_type_for_literal_widening(
                            expanded_program_id,
                            expanded,
                        )
                    })
                    .unwrap_or(return_type)
            }
            TyKind::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.inference_return_type_for_literal_widening(program_id, *ty)),
            ),
            TyKind::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection
                    .types
                    .iter()
                    .filter(|ty| {
                        !matches!(
                            self.ty_kind(**ty),
                            TyKind::Object(object) if object.is_empty()
                        )
                    })
                    .map(|ty| self.inference_return_type_for_literal_widening(program_id, *ty)),
            ),
            _ => return_type,
        }
    }
}

struct ReturnExpressionVisitor<'a> {
    return_expressions: Vec<&'a Expression<'a>>,
    yield_expressions: Vec<&'a Expression<'a>>,
}

impl<'a> ReturnExpressionVisitor<'a> {
    /// Collect return expressions from this function body, ignoring nested functions.
    fn expressions_in_body(body: &'a FunctionBody<'a>) -> ReturnExpressionVisitor<'a> {
        let mut visitor = Self {
            return_expressions: Vec::new(),
            yield_expressions: Vec::new(),
        };
        visitor.visit_function_body(body);
        visitor
    }
}

impl<'a> Visit<'a> for ReturnExpressionVisitor<'a> {
    fn visit_return_statement(&mut self, statement: &ReturnStatement<'a>) {
        if let Some(argument) = statement.argument.as_ref() {
            self.return_expressions.push(self.alloc(argument));
        }
    }

    fn visit_yield_expression(&mut self, expression: &YieldExpression<'a>) {
        if let Some(argument) = expression.argument.as_ref() {
            self.yield_expressions.push(self.alloc(argument));
        }
    }

    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(&mut self, _function: &ArrowFunctionExpression<'a>) {}
}

fn match_property_type_pairs<'a>(
    source_properties: impl IntoIterator<Item = TyProperty<'a>>,
    target_properties: impl IntoIterator<Item = TyProperty<'a>>,
    mode: PropertyMatchMode,
) -> Option<Vec<(Ty<'a>, Ty<'a>)>> {
    let source_properties = source_properties.into_iter().collect::<Vec<_>>();
    let mut pairs = Vec::new();

    for target_property in target_properties {
        let Some(source_property) = source_properties.iter().find(|source_property| {
            source_property.name == target_property.name
                && source_property.computed == target_property.computed
        }) else {
            match mode {
                PropertyMatchMode::ExistingOnly | PropertyMatchMode::RequireTarget
                    if target_property.optional =>
                {
                    continue;
                }
                PropertyMatchMode::ExistingOnly => continue,
                PropertyMatchMode::RequireTarget => return None,
            }
        };
        if mode == PropertyMatchMode::RequireTarget
            && source_property.optional
            && !target_property.optional
        {
            return None;
        }
        pairs.push((source_property.ty, target_property.ty));
    }

    Some(pairs)
}

impl<'a, 'store> Checker<'a, 'store> {
    fn infer_type_pairs_with_variance(
        &self,
        pairs: impl IntoIterator<Item = (Ty<'a>, Ty<'a>)>,
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
        priority: InferencePriority,
    ) {
        for (parameter_type, argument_type) in pairs {
            self.infer_types_with_variance(
                parameter_type,
                argument_type,
                context,
                variance,
                priority,
            );
        }
    }

    fn infer_types(
        &self,
        parameter_type: Ty<'a>,
        argument_type: Ty<'a>,
        context: &mut InferenceContext<'a>,
    ) {
        self.infer_types_with_variance(
            parameter_type,
            argument_type,
            context,
            InferenceVariance::Covariant,
            InferencePriority::NakedTypeVariable,
        );
    }

    fn infer_types_with_variance(
        &self,
        parameter_type: Ty<'a>,
        argument_type: Ty<'a>,
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
        priority: InferencePriority,
    ) {
        let arena = self.arena();
        match (self.ty_kind(parameter_type), self.ty_kind(argument_type)) {
            (TyKind::Union(parameter_union), _) => {
                self.infer_type_parameter_from_union(
                    parameter_union.types.iter().copied(),
                    argument_type,
                    context,
                    variance,
                    priority,
                );
            }
            (TyKind::Intersection(parameter_intersection), _) => {
                self.infer_type_parameter_from_intersection(
                    parameter_intersection.types.iter().copied(),
                    argument_type,
                    context,
                    variance,
                    priority,
                );
            }
            (TyKind::Array(parameter_array), TyKind::Array(argument_array)) => {
                self.infer_types_with_variance(
                    parameter_array.element_type,
                    argument_array.element_type,
                    context,
                    variance,
                    priority.structural(),
                );
            }
            (TyKind::Tuple(parameter_tuple), TyKind::Tuple(argument_tuple)) => {
                self.infer_tuple_elements(
                    &parameter_tuple.elements,
                    &argument_tuple.elements,
                    context,
                    variance,
                    priority.structural(),
                );
            }
            (TyKind::Keyof(parameter_keyof), TyKind::Keyof(argument_keyof)) => {
                self.infer_types_with_variance(
                    parameter_keyof.target,
                    argument_keyof.target,
                    context,
                    variance,
                    priority.structural(),
                );
            }
            (TyKind::IndexedAccess(parameter_indexed), TyKind::IndexedAccess(argument_indexed)) => {
                self.infer_types_with_variance(
                    parameter_indexed.object_type,
                    argument_indexed.object_type,
                    context,
                    variance,
                    priority.structural(),
                );
                self.infer_types_with_variance(
                    parameter_indexed.index_type,
                    argument_indexed.index_type,
                    context,
                    variance,
                    priority.structural(),
                );
            }
            (TyKind::IndexedAccess(parameter_indexed), _) => {
                if let Some(simplified) = self.simplify_indexed_access_for_inference(
                    parameter_indexed.object_type,
                    parameter_indexed.index_type,
                    context,
                ) {
                    self.infer_types_with_variance(
                        simplified,
                        argument_type,
                        context,
                        variance,
                        priority.structural(),
                    );
                }
            }
            (TyKind::Mapped(parameter_mapped), _) => self.infer_to_mapped_type(
                parameter_mapped,
                argument_type,
                context,
                variance,
                priority,
            ),
            (_, TyKind::TypeQuery(argument_query)) => self.infer_types_with_variance(
                parameter_type,
                argument_query.resolved,
                context,
                variance,
                priority.structural(),
            ),
            (TyKind::TypeReference(reference), _) if reference.is_bare() => {
                let Some(type_parameter) = context
                    .inference_by_name_mut(reference.name)
                    .map(|inference| inference.type_parameter)
                else {
                    return;
                };
                context.add_candidate(type_parameter, argument_type, priority, variance)
            }
            (
                TyKind::TypeReference(parameter_reference),
                TyKind::TypeReference(argument_reference),
            ) if parameter_reference.name == argument_reference.name => {
                self.infer_type_pairs_with_variance(
                    parameter_reference
                        .type_arguments
                        .iter()
                        .copied()
                        .zip(argument_reference.type_arguments.iter().copied()),
                    context,
                    variance,
                    priority.structural(),
                );
            }
            (TyKind::Object(parameter_object), TyKind::Object(argument_object)) => {
                if let Some(pairs) = match_property_type_pairs(
                    argument_object.properties.iter().copied(),
                    parameter_object.properties.iter().copied(),
                    PropertyMatchMode::ExistingOnly,
                ) {
                    self.infer_type_pairs_with_variance(
                        pairs
                            .into_iter()
                            .map(|(argument, parameter)| (parameter, argument)),
                        context,
                        variance,
                        priority.structural(),
                    );
                }
                for parameter_index in parameter_object.index_infos() {
                    if let Some(argument_index) =
                        argument_object.index_infos().iter().find(|argument_index| {
                            arena.is_type_identical_to(
                                parameter_index.key_type,
                                argument_index.key_type,
                            )
                        })
                    {
                        self.infer_types_with_variance(
                            parameter_index.value_type,
                            argument_index.value_type,
                            context,
                            variance,
                            priority.structural(),
                        );
                    }
                }
            }
            (TyKind::Function(parameter_function), TyKind::Function(argument_function)) => {
                self.infer_from_signature_types(
                    parameter_function,
                    argument_function,
                    context,
                    variance,
                    priority,
                );
            }
            _ => {}
        }
    }

    fn infer_from_signature_types(
        &self,
        parameter_function: &TyFunction<'a>,
        argument_function: &TyFunction<'a>,
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
        priority: InferencePriority,
    ) {
        for (parameter, argument) in parameter_function
            .parameters
            .iter()
            .zip(argument_function.parameters.iter())
        {
            self.infer_types_with_variance(
                parameter.ty,
                argument.ty,
                context,
                variance.flip(),
                priority.structural(),
            );
        }

        if type_contains_inference_variable(self.arena(), parameter_function.return_type, context) {
            self.infer_types_with_variance(
                parameter_function.return_type,
                argument_function.return_type,
                context,
                variance,
                priority.return_type(),
            );
        }
    }
}

fn type_contains_inference_variable<'a>(
    arena: CheckerArena<'a>,
    ty: Ty<'a>,
    context: &InferenceContext<'a>,
) -> bool {
    let mut contains = false;
    visit_type(arena, ty, &mut |ty| {
        if let TyKind::TypeReference(reference) = arena.ty_kind(ty)
            && reference.is_bare()
            && context.contains_type_parameter_name(reference.name)
        {
            contains = true;
        }
    });
    contains
}

impl<'a, 'store> Checker<'a, 'store> {
    fn infer_to_mapped_type(
        &self,
        parameter_mapped: &TyMapped<'a>,
        argument_type: Ty<'a>,
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
        priority: InferencePriority,
    ) {
        self.infer_to_mapped_type_with_constraint(
            parameter_mapped,
            parameter_mapped.constraint,
            argument_type,
            context,
            variance,
            priority,
        );
    }

    fn simplify_indexed_access_for_inference(
        &self,
        object_type: Ty<'a>,
        index_type: Ty<'a>,
        context: &mut InferenceContext<'a>,
    ) -> Option<Ty<'a>> {
        let arena = self.arena();
        let substitutions = context.candidate_substitutions(self);
        let mapper = substitutions.to_mapper(arena);
        let object_type = substitute_type(object_type, &mapper, arena);
        let index_type = substitute_type(index_type, &mapper, arena);

        resolve_indexed_access_for_inference(object_type, index_type, arena)
    }
}

fn resolve_indexed_access_for_inference<'a>(
    object_type: Ty<'a>,
    index_type: Ty<'a>,
    arena: crate::types::CheckerArena<'a>,
) -> Option<Ty<'a>> {
    if let TyKind::Array(array) = arena.ty_kind(object_type)
        && index_type.is_number_like(arena)
    {
        return Some(array.element_type);
    }

    if let TyKind::Tuple(tuple) = arena.ty_kind(object_type)
        && let TyKind::NumberLiteral(literal) = arena.ty_kind(index_type)
        && let Some(index) = literal.value.to_usize()
    {
        return tuple.elements.get(index).map(TupleElement::ty);
    }

    if let TyKind::Union(union) = arena.ty_kind(index_type) {
        let property_types = union
            .types
            .iter()
            .map(|index_type| resolve_indexed_access_for_inference(object_type, *index_type, arena))
            .collect::<Option<Vec<_>>>()?;
        Some(Ty::union(arena, property_types))
    } else {
        let property_name = index_type_to_property_name(arena, index_type)?;
        property_type_for_inference_index(object_type, property_name, arena)
    }
}

fn property_type_for_inference_index<'a>(
    object_type: Ty<'a>,
    property_name: &str,
    arena: crate::types::CheckerArena<'a>,
) -> Option<Ty<'a>> {
    match arena.ty_kind(object_type) {
        TyKind::Object(object) => object.properties.iter().find_map(|property| {
            if property.computed || property.name != property_name {
                return None;
            }
            Some(if property.optional {
                Ty::union(arena, [property.ty, Ty::undefined()])
            } else {
                property.ty
            })
        }),
        TyKind::Union(union) => {
            let property_types = union
                .types
                .iter()
                .map(|ty| property_type_for_inference_index(*ty, property_name, arena))
                .collect::<Option<Vec<_>>>()?;
            Some(Ty::union(arena, property_types))
        }
        TyKind::Intersection(intersection) => intersection
            .types
            .iter()
            .find_map(|ty| property_type_for_inference_index(*ty, property_name, arena)),
        _ => None,
    }
}

impl<'a, 'store> Checker<'a, 'store> {
    fn infer_to_mapped_type_with_constraint(
        &self,
        parameter_mapped: &TyMapped<'a>,
        constraint_type: Ty<'a>,
        argument_type: Ty<'a>,
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
        priority: InferencePriority,
    ) {
        let arena = self.arena();
        // A same-shape mapped type, also called a homomorphic mapped type in
        // TypeScript terminology, is the common utility-type shape that maps directly
        // over the keys of a source type, for example:
        //
        //     { [P in keyof T]: T[P] }
        //     Partial<T>  // { [P in keyof T]?: T[P] }
        //     Readonly<T> // { readonly [P in keyof T]: T[P] }
        //
        // The important part is the `keyof T` constraint: the mapped type preserves the
        // source type's property set, so inference can recover information about `T`
        // instead of treating the mapped object as unrelated structure.
        //
        // If both sides are same-shape mapped types, infer from their `keyof` targets
        // with `SameShapeMappedType` priority. If the argument is an ordinary object,
        // reconstruct a same-shaped source candidate for the mapped target. That is the
        // first reverse-mapped inference case: from `{ value: number }` and
        // `{ [P in keyof T]: T[P] }`, infer `T` as `{ value: number }`.
        let Some(parameter_target) = same_shape_mapped_constraint_target(arena, constraint_type)
        else {
            return self.infer_to_non_homomorphic_mapped_type(
                parameter_mapped,
                constraint_type,
                argument_type,
                context,
                variance,
                priority,
            );
        };

        match self.ty_kind(argument_type) {
            TyKind::Mapped(argument_mapped) => {
                if let Some(argument_target) = same_shape_mapped_type_target(arena, argument_mapped)
                {
                    self.infer_types_with_variance(
                        parameter_target,
                        argument_target,
                        context,
                        variance,
                        InferencePriority::SameShapeMappedType,
                    );
                } else {
                    self.infer_types_with_variance(
                        parameter_mapped.constraint,
                        argument_mapped.constraint,
                        context,
                        variance,
                        priority.structural(),
                    );
                }
            }
            TyKind::Object(argument_object) => {
                self.infer_reverse_mapped_source_type(
                    parameter_mapped,
                    parameter_target,
                    Ty::object(arena, argument_object.properties.iter().copied()),
                    argument_object.properties.iter().copied(),
                    context,
                    variance,
                );
            }
            TyKind::Array(argument_array) => {
                let reverse_candidate = if argument_array.readonly {
                    Ty::readonly_array(arena, argument_array.element_type)
                } else {
                    Ty::array(arena, argument_array.element_type)
                };
                self.infer_reverse_mapped_source_type(
                    parameter_mapped,
                    parameter_target,
                    reverse_candidate,
                    [Ty::property("0", argument_array.element_type)],
                    context,
                    variance,
                );
            }
            TyKind::Tuple(argument_tuple) => {
                let elements = argument_tuple
                    .elements
                    .iter()
                    .map(|element| reverse_mapped_tuple_element(*element, parameter_mapped, arena))
                    .collect::<Vec<_>>();
                let reverse_candidate = Ty::tuple_with_labels(
                    arena,
                    elements,
                    argument_tuple.labels.iter().copied().collect(),
                    argument_tuple.readonly,
                );
                let properties =
                    argument_tuple
                        .elements
                        .iter()
                        .enumerate()
                        .map(|(index, element)| {
                            Ty::property(arena.str(&index.to_string()), element.ty())
                        });
                self.infer_reverse_mapped_source_type(
                    parameter_mapped,
                    parameter_target,
                    reverse_candidate,
                    properties,
                    context,
                    variance,
                );
            }
            _ => self.infer_types_with_variance(
                constraint_type,
                argument_type,
                context,
                variance,
                priority.structural(),
            ),
        }
    }

    fn infer_to_non_homomorphic_mapped_type(
        &self,
        parameter_mapped: &TyMapped<'a>,
        constraint_type: Ty<'a>,
        argument_type: Ty<'a>,
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
        priority: InferencePriority,
    ) {
        let arena = self.arena();
        match self.ty_kind(constraint_type) {
            TyKind::Union(union) => {
                for constraint in &union.types {
                    self.infer_to_mapped_type_with_constraint(
                        parameter_mapped,
                        *constraint,
                        argument_type,
                        context,
                        variance,
                        priority,
                    );
                }
            }
            TyKind::Intersection(intersection) => {
                for constraint in &intersection.types {
                    self.infer_to_mapped_type_with_constraint(
                        parameter_mapped,
                        *constraint,
                        argument_type,
                        context,
                        variance,
                        priority,
                    );
                }
            }
            TyKind::TypeReference(reference) if reference.is_bare() => {
                let key_type = Ty::keyof(arena, argument_type);
                self.infer_types_with_variance(
                    constraint_type,
                    key_type,
                    context,
                    variance,
                    InferencePriority::MappedTypeConstraint,
                );
                if let Some(extended_constraint) = context
                    .type_parameter_by_name(reference.name)
                    .and_then(|type_parameter| type_parameter.constraint_type)
                {
                    self.infer_to_mapped_type_with_constraint(
                        parameter_mapped,
                        extended_constraint,
                        argument_type,
                        context,
                        variance,
                        priority,
                    );
                } else if let Some(property_types) = inferable_property_types(arena, argument_type)
                {
                    self.infer_types_with_variance(
                        parameter_mapped.template,
                        Ty::union(arena, property_types),
                        context,
                        variance,
                        priority.structural(),
                    );
                }
            }
            _ => self.infer_types_with_variance(
                constraint_type,
                argument_type,
                context,
                variance,
                priority.structural(),
            ),
        }
    }

    fn infer_reverse_mapped_source_type(
        &self,
        parameter_mapped: &TyMapped<'a>,
        parameter_target: Ty<'a>,
        reverse_candidate: Ty<'a>,
        argument_properties: impl IntoIterator<Item = TyProperty<'a>>,
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
    ) {
        let arena = self.arena();
        let argument_properties = argument_properties.into_iter().collect::<Vec<_>>();

        self.infer_types_with_variance(
            parameter_target,
            reverse_candidate,
            context,
            variance,
            InferencePriority::SameShapeMappedType,
        );

        for property in argument_properties {
            if property.computed {
                continue;
            }
            let key_mapper = TypeMapper::single(
                Ty::type_reference(arena, parameter_mapped.key, std::iter::empty()),
                Ty::string_literal(arena, property.name),
            );
            let template_at_key = substitute_type(parameter_mapped.template, &key_mapper, arena);
            self.infer_types_with_variance(
                template_at_key,
                property.ty,
                context,
                variance,
                InferencePriority::SameShapeMappedType,
            );
        }
    }
}

fn reverse_mapped_tuple_element<'a>(
    element: TupleElement<'a>,
    mapped: &TyMapped<'a>,
    arena: crate::types::CheckerArena<'a>,
) -> TupleElement<'a> {
    match element {
        TupleElement::Optional(ty)
            if matches!(mapped.optional, MappedModifier::True | MappedModifier::Plus) =>
        {
            TupleElement::Regular(remove_undefined_from_type(ty, arena))
        }
        _ => element,
    }
}

// TODO(cleanup): use `remove_undefined` from checker
fn remove_undefined_from_type<'a>(ty: Ty<'a>, arena: crate::types::CheckerArena<'a>) -> Ty<'a> {
    ty.map_union(arena, |ty| (ty != Ty::Undefined).then_some(ty))
}

fn inferable_property_types<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> Option<Vec<Ty<'a>>> {
    match arena.ty_kind(ty) {
        TyKind::Object(object) => Some(
            object
                .properties
                .iter()
                .map(|property| property.ty)
                .collect(),
        ),
        TyKind::Array(array) => Some(vec![array.element_type]),
        TyKind::Tuple(tuple) => Some(tuple.elements.iter().map(TupleElement::ty).collect()),
        _ => None,
    }
}

fn substitute_type<'a>(
    ty: Ty<'a>,
    mapper: &TypeMapper<'a>,
    arena: crate::types::CheckerArena<'a>,
) -> Ty<'a> {
    match arena.ty_kind(ty) {
        TyKind::TypeReference(reference) => {
            let mapped = mapper.map(arena, ty);
            if mapped != ty {
                mapped
            } else {
                Ty::type_reference(
                    arena,
                    reference.name,
                    reference
                        .type_arguments
                        .iter()
                        .map(|ty| substitute_type(*ty, mapper, arena)),
                )
            }
        }
        TyKind::IndexedAccess(indexed_access) => Ty::indexed_access(
            arena,
            substitute_type(indexed_access.object_type, mapper, arena),
            substitute_type(indexed_access.index_type, mapper, arena),
        ),
        TyKind::Keyof(keyof) => Ty::keyof(arena, substitute_type(keyof.target, mapper, arena)),
        TyKind::Array(array) => {
            Ty::array(arena, substitute_type(array.element_type, mapper, arena))
        }
        TyKind::Tuple(tuple) => Ty::tuple_with_labels(
            arena,
            tuple
                .elements
                .iter()
                .map(|element| element.map_ty(|ty| substitute_type(ty, mapper, arena)))
                .collect(),
            tuple.labels.iter().copied().collect(),
            tuple.readonly,
        ),
        TyKind::Union(union) => Ty::union(
            arena,
            union
                .types
                .iter()
                .map(|ty| substitute_type(*ty, mapper, arena)),
        ),
        TyKind::Intersection(intersection) => Ty::intersection(
            arena,
            intersection
                .types
                .iter()
                .map(|ty| substitute_type(*ty, mapper, arena)),
        ),
        _ => mapper.map(arena, ty),
    }
}

fn same_shape_mapped_type_target<'a>(
    arena: CheckerArena<'a>,
    mapped: &TyMapped<'a>,
) -> Option<Ty<'a>> {
    // In this checker's `TyMapped` representation, the TypeScript shape
    // `{ [P in keyof T]: ... }` is represented as `constraint = Ty::Keyof(T)`.
    // A key remapping clause (`as ...`) means the mapped type may no longer preserve
    // exactly the source key set, so keep those out of the same-shape bucket for now.
    if mapped.name_type.is_some() {
        return None;
    }
    same_shape_mapped_constraint_target(arena, mapped.constraint)
}

fn same_shape_mapped_constraint_target<'a>(
    arena: CheckerArena<'a>,
    constraint: Ty<'a>,
) -> Option<Ty<'a>> {
    let TyKind::Keyof(keyof) = arena.ty_kind(constraint) else {
        return None;
    };
    Some(keyof.target)
}

impl<'a, 'store> Checker<'a, 'store> {
    fn infer_tuple_elements(
        &self,
        parameter_elements: &[TupleElement<'a>],
        argument_elements: &[TupleElement<'a>],
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
        priority: InferencePriority,
    ) {
        let arena = self.arena();
        if let Some((rest_index, TupleElement::Rest(rest_type))) = parameter_elements
            .iter()
            .enumerate()
            .find(|(_, element)| matches!(element, TupleElement::Rest(_)))
        {
            if rest_index + 1 != parameter_elements.len() || argument_elements.len() < rest_index {
                return;
            }
            for (parameter, argument) in parameter_elements
                .iter()
                .take(rest_index)
                .zip(argument_elements.iter())
            {
                self.infer_types_with_variance(
                    parameter.ty(),
                    argument.ty(),
                    context,
                    variance,
                    priority,
                );
            }
            let rest_tuple = Ty::tuple(
                arena,
                argument_elements
                    .iter()
                    .skip(rest_index)
                    .copied()
                    .collect::<Vec<_>>(),
            );
            self.infer_types_with_variance(*rest_type, rest_tuple, context, variance, priority);
            return;
        }

        if parameter_elements.len() != argument_elements.len() {
            return;
        }

        for (parameter, argument) in parameter_elements.iter().zip(argument_elements.iter()) {
            self.infer_types_with_variance(
                parameter.ty(),
                argument.ty(),
                context,
                variance,
                priority,
            );
        }
    }

    fn infer_type_parameter_from_union(
        &self,
        parameter_types: impl IntoIterator<Item = Ty<'a>>,
        argument_type: Ty<'a>,
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
        priority: InferencePriority,
    ) {
        let arena = self.arena();
        let parameter_types = parameter_types
            .into_iter()
            .filter(|ty| *ty != Ty::Null && *ty != Ty::Undefined && *ty != Ty::Never)
            .collect::<Vec<_>>();

        let candidates =
            select_union_inference_candidates(arena, &parameter_types, argument_type, context);

        for candidate in candidates {
            self.infer_types_with_variance(candidate, argument_type, context, variance, priority);
        }
    }
}

fn select_union_inference_candidates<'a>(
    arena: CheckerArena<'a>,
    parameter_types: &[Ty<'a>],
    argument_type: Ty<'a>,
    context: &InferenceContext<'a>,
) -> Vec<Ty<'a>> {
    let structurally_matching = match arena.ty_kind(argument_type) {
        _ if argument_type.is_function(arena) => parameter_types
            .iter()
            .copied()
            .filter(|ty| ty.is_function(arena))
            .collect(),
        TyKind::TypeReference(argument_reference) => parameter_types
            .iter()
            .copied()
            .filter(|ty| {
                matches!(arena.ty_kind(*ty), TyKind::TypeReference(parameter_reference) if parameter_reference.name == argument_reference.name)
            })
            .collect(),
        TyKind::Array(_) => parameter_types
            .iter()
            .copied()
            .filter(|ty| matches!(arena.ty_kind(*ty), TyKind::Array(_)))
            .collect(),
        TyKind::Tuple(_) => parameter_types
            .iter()
            .copied()
            .filter(|ty| matches!(arena.ty_kind(*ty), TyKind::Tuple(_)))
            .collect(),
        _ => Vec::new(),
    };
    if !structurally_matching.is_empty() {
        return structurally_matching;
    }

    let naked_type_variables = parameter_types
        .iter()
        .copied()
        .filter(|ty| {
            matches!(arena.ty_kind(*ty), TyKind::TypeReference(reference) if reference.is_bare() && context.contains_type_parameter_name(reference.name))
        })
        .collect::<Vec<_>>();
    if !naked_type_variables.is_empty() {
        return naked_type_variables;
    }

    parameter_types.to_vec()
}

impl<'a, 'store> Checker<'a, 'store> {
    fn infer_type_parameter_from_intersection(
        &self,
        parameter_types: impl IntoIterator<Item = Ty<'a>>,
        argument_type: Ty<'a>,
        context: &mut InferenceContext<'a>,
        variance: InferenceVariance,
        priority: InferencePriority,
    ) {
        let arena = self.arena();
        let parameter_types = parameter_types.into_iter().collect::<Vec<_>>();
        let mut argument_types = match self.ty_kind(argument_type) {
            TyKind::Intersection(intersection) => {
                intersection.types.iter().copied().collect::<Vec<_>>()
            }
            _ => vec![argument_type],
        };

        let mut unmatched_parameters = Vec::new();
        let mut removed_match = false;
        for parameter in parameter_types {
            if let Some(index) = argument_types
                .iter()
                .position(|argument| arena.is_type_identical_to(*argument, parameter))
            {
                argument_types.remove(index);
                removed_match = true;
            } else {
                unmatched_parameters.push(parameter);
            }
        }

        if !removed_match || argument_types.is_empty() || unmatched_parameters.is_empty() {
            return;
        }

        let argument_remainder = Ty::intersection(arena, argument_types);
        let parameter_remainder = Ty::intersection(arena, unmatched_parameters);
        self.infer_types_with_variance(
            parameter_remainder,
            argument_remainder,
            context,
            variance,
            priority.structural(),
        );
    }
}

fn ts_signature_contains_infer(signature: &TSSignature<'_>) -> bool {
    match signature {
        TSSignature::TSPropertySignature(property) => property
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation)),
        TSSignature::TSMethodSignature(method) => {
            formal_parameters_contain_infer(method.params.as_ref())
                || method
                    .return_type
                    .as_deref()
                    .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
        }
        TSSignature::TSCallSignatureDeclaration(signature) => {
            formal_parameters_contain_infer(signature.params.as_ref())
                || signature
                    .return_type
                    .as_deref()
                    .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
        }
        TSSignature::TSConstructSignatureDeclaration(signature) => {
            formal_parameters_contain_infer(signature.params.as_ref())
                || signature
                    .return_type
                    .as_deref()
                    .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
        }
        _ => false,
    }
}

fn formal_parameters_contain_infer(parameters: &FormalParameters<'_>) -> bool {
    parameters.items.iter().any(|parameter| {
        parameter
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
    }) || parameters.rest.as_ref().is_some_and(|parameter| {
        parameter
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
    })
}

pub fn ts_type_contains_infer(ty: &TSType<'_>) -> bool {
    match ty {
        TSType::TSInferType(_) => true,
        TSType::TSArrayType(array) => ts_type_contains_infer(&array.element_type),
        TSType::TSTupleType(tuple) => tuple.element_types.iter().any(|element| match element {
            TSTupleElement::TSRestType(rest) => ts_type_contains_infer(&rest.type_annotation),
            TSTupleElement::TSOptionalType(optional) => {
                ts_type_contains_infer(&optional.type_annotation)
            }
            _ => element.as_ts_type().is_some_and(ts_type_contains_infer),
        }),
        TSType::TSUnionType(union) => union.types.iter().any(|ty| ts_type_contains_infer(ty)),
        TSType::TSIntersectionType(intersection) => intersection
            .types
            .iter()
            .any(|ty| ts_type_contains_infer(ty)),
        TSType::TSParenthesizedType(parenthesized) => {
            ts_type_contains_infer(&parenthesized.type_annotation)
        }
        TSType::TSTypeOperatorType(operator) => ts_type_contains_infer(&operator.type_annotation),
        TSType::TSIndexedAccessType(indexed_access) => {
            ts_type_contains_infer(&indexed_access.object_type)
                || ts_type_contains_infer(&indexed_access.index_type)
        }
        TSType::TSConditionalType(conditional) => {
            ts_type_contains_infer(&conditional.check_type)
                || ts_type_contains_infer(&conditional.extends_type)
                || ts_type_contains_infer(&conditional.true_type)
                || ts_type_contains_infer(&conditional.false_type)
        }
        TSType::TSTypeReference(reference) => {
            reference
                .type_arguments
                .as_ref()
                .is_some_and(|type_arguments| {
                    type_arguments
                        .params
                        .iter()
                        .any(|ty| ts_type_contains_infer(ty))
                })
        }
        TSType::TSFunctionType(function) => {
            formal_parameters_contain_infer(function.params.as_ref())
                || ts_type_contains_infer(&function.return_type.type_annotation)
        }
        TSType::TSTypeLiteral(type_literal) => {
            type_literal.members.iter().any(ts_signature_contains_infer)
        }
        TSType::TSMappedType(mapped) => {
            ts_type_contains_infer(&mapped.constraint)
                || mapped
                    .name_type
                    .as_ref()
                    .is_some_and(|ty| ts_type_contains_infer(ty))
                || mapped
                    .type_annotation
                    .as_ref()
                    .is_some_and(|ty| ts_type_contains_infer(ty))
        }
        TSType::TSTypePredicate(predicate) => predicate
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation)),
        _ => false,
    }
}

#[cfg(test)]
#[path = "infer_test.rs"]
mod infer_test;
