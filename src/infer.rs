use oxc_ast::ast::{
    ArrowFunctionExpression, CallExpression, Expression, FormalParameters, Function, FunctionBody,
    NewExpression, ReturnStatement, TSSignature, TSTupleElement, TSType,
    TSTypeParameterInstantiation, YieldExpression,
};
use oxc_ast_visit::Visit;
use oxc_semantic::{NodeId, ScopeFlags};
use std::cell::RefCell;

use crate::{
    checker::CheckerReturn,
    checker_impl::{FunctionKind, GetTypeFlags},
    index_type_to_property_name,
    limits::{
        CONDITIONAL_INFER_MATCH_MAX_DEPTH, CONDITIONAL_TYPE_DEPTH, CONDITIONAL_TYPE_MAX_DEPTH,
    },
    mapper::{TypeMapper, TypeParameterSubstitutions},
    program::ProgramId,
    relations::is_assignable_to_without_checker,
    types::{
        MappedModifier, TupleElement, Ty, TyConditional, TyFunction, TyInfer, TyMapped, TyProperty,
        TyTypeParameter, function_parameter_type_at_call_index, visit_type,
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
pub(crate) enum InferencePriority {
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
pub(crate) struct InferenceResolutionFlags {
    fill_unresolved_with_unknown: bool,
}

impl InferenceResolutionFlags {
    pub(crate) const NONE: Self = Self {
        fill_unresolved_with_unknown: false,
    };

    pub(crate) const FILL_UNRESOLVED_WITH_UNKNOWN: Self = Self {
        fill_unresolved_with_unknown: true,
    };

    fn fill_unresolved_with_unknown(self) -> bool {
        self.fill_unresolved_with_unknown
    }
}

#[derive(Clone, Debug)]
pub(crate) struct InferenceInfo<'a> {
    pub(crate) type_parameter: TyTypeParameter<'a>,
    pub(crate) candidates: Vec<Ty<'a>>,
    pub(crate) contra_candidates: Vec<Ty<'a>>,
    pub(crate) inferred_type: Option<Ty<'a>>,
    pub(crate) priority: InferencePriority,
    pub(crate) top_level: bool,
    pub(crate) is_fixed: bool,
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

#[derive(Clone, Debug)]
pub(crate) struct InferenceContext<'a> {
    inferences: Vec<InferenceInfo<'a>>,
    return_type: Option<Ty<'a>>,
}

pub(crate) struct InferenceResolution<'a> {
    substitutions: TypeParameterSubstitutions<'a>,
    mapper: TypeMapper<'a>,
}

impl<'a> InferenceResolution<'a> {
    fn new(
        substitutions: TypeParameterSubstitutions<'a>,
        arena: crate::types::CheckerArena<'a>,
    ) -> Self {
        let mapper = substitutions.to_inference_mapper(arena);
        Self::new_with_mapper(substitutions, mapper)
    }

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
    pub(crate) fn with_substitutions(
        type_parameters: impl IntoIterator<Item = TyTypeParameter<'a>>,
        substitutions: &TypeParameterSubstitutions<'a>,
    ) -> Self {
        Self {
            inferences: type_parameters
                .into_iter()
                .map(|type_parameter| {
                    InferenceInfo::new(type_parameter, substitutions.get(type_parameter))
                })
                .collect(),
            return_type: None,
        }
    }

    pub(crate) fn with_return_type(mut self, return_type: Ty<'a>) -> Self {
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

    pub(crate) fn add_candidate(
        &mut self,
        type_parameter: TyTypeParameter<'a>,
        candidate: Ty<'a>,
        priority: InferencePriority,
    ) {
        let Some(inference) = self.inference_for_type_parameter_mut(type_parameter) else {
            return;
        };
        if inference.is_fixed {
            return;
        }
        if priority > inference.priority {
            inference.candidates.clear();
            inference.priority = priority;
        } else if priority < inference.priority {
            return;
        }
        inference.top_level |= priority == InferencePriority::NakedTypeVariable;
        if !inference.candidates.contains(&candidate) {
            inference.candidates.push(candidate);
            inference.inferred_type = None;
        }
    }

    pub(crate) fn add_contra_candidate(
        &mut self,
        type_parameter: TyTypeParameter<'a>,
        candidate: Ty<'a>,
        priority: InferencePriority,
    ) {
        let Some(inference) = self.inference_for_type_parameter_mut(type_parameter) else {
            return;
        };
        if inference.is_fixed {
            return;
        }
        if priority > inference.priority {
            inference.candidates.clear();
            inference.contra_candidates.clear();
            inference.priority = priority;
        } else if priority < inference.priority {
            return;
        }
        inference.top_level |= priority == InferencePriority::NakedTypeVariable;
        if !inference.contra_candidates.contains(&candidate) {
            inference.contra_candidates.push(candidate);
            inference.inferred_type = None;
        }
    }

    pub(crate) fn resolve(
        mut self,
        arena: crate::types::CheckerArena<'a>,
        flags: InferenceResolutionFlags,
    ) -> InferenceResolution<'a> {
        let mut substitutions = TypeParameterSubstitutions::new();

        for index in 0..self.inferences.len() {
            if let Some(inferred_type) =
                self.resolve_inference_at_index(index, arena, flags, &mut Vec::new(), false)
            {
                substitutions.insert(self.inferences[index].type_parameter, inferred_type);
            }
        }
        InferenceResolution::new(substitutions, arena)
    }

    pub(crate) fn resolve_with_contextual_mapper(
        self,
        arena: crate::types::CheckerArena<'a>,
        flags: InferenceResolutionFlags,
    ) -> InferenceResolution<'a> {
        let contextual_context = self.clone();
        let snapshot_resolution = self.resolve(arena, flags);
        let contextual_pairs = contextual_context
            .inferences
            .iter()
            .map(|inference| {
                let source =
                    Ty::type_reference(arena, inference.type_parameter.name, std::iter::empty());
                let fallback_target = snapshot_resolution
                    .substitutions
                    .get(inference.type_parameter)
                    .unwrap_or(source);
                (source, fallback_target)
            })
            .collect::<Vec<_>>();
        let contextual_context = RefCell::new(contextual_context);
        let mapper =
            TypeMapper::from_contextual_inference_pairs(arena, contextual_pairs, move |name| {
                contextual_context
                    .borrow_mut()
                    .resolve_type_parameter_by_name(name, arena, flags)
            });
        InferenceResolution::new_with_mapper(snapshot_resolution.substitutions, mapper)
    }

    pub(crate) fn resolve_type_parameter_by_name(
        &mut self,
        name: &str,
        arena: crate::types::CheckerArena<'a>,
        flags: InferenceResolutionFlags,
    ) -> Option<Ty<'a>> {
        let index = self.inference_index_by_name(name)?;
        self.resolve_inference_at_index(index, arena, flags, &mut Vec::new(), true)
    }

    fn resolve_inference_at_index(
        &mut self,
        index: usize,
        arena: crate::types::CheckerArena<'a>,
        flags: InferenceResolutionFlags,
        resolving: &mut Vec<usize>,
        fix: bool,
    ) -> Option<Ty<'a>> {
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
        let mut inferred_type = self.get_inferred_type(index, arena);

        if inferred_type.is_none()
            && let Some(fallback_type) = self.inferences[index]
                .type_parameter
                .default_type
                .or(self.inferences[index].type_parameter.constraint_type)
        {
            for dependency_index in self.fallback_dependency_indices(fallback_type) {
                if dependency_index < index {
                    self.resolve_inference_at_index(
                        dependency_index,
                        arena,
                        flags,
                        resolving,
                        true,
                    );
                }
            }
            let substitutions = self.fallback_substitutions(index, fallback_type);
            let fallback_type =
                instantiate_inference_fallback_type(fallback_type, &substitutions, arena);
            self.inferences[index].inferred_type = Some(fallback_type);
            inferred_type = Some(fallback_type);
        }

        if let Some(current_inferred_type) = inferred_type
            && let Some(constraint_type) = self.inferences[index].type_parameter.constraint_type
        {
            let substitutions = self.resolved_substitutions();
            let constraint_type =
                instantiate_inference_fallback_type(constraint_type, &substitutions, arena);
            if !is_assignable_to_without_checker(current_inferred_type, constraint_type) {
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
        current_index: usize,
        fallback_type: Ty<'a>,
    ) -> TypeParameterSubstitutions<'a> {
        let mut substitutions = self.resolved_substitutions();
        for dependency_index in self.fallback_dependency_indices(fallback_type) {
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

    fn fallback_dependency_indices(&self, fallback_type: Ty<'a>) -> Vec<usize> {
        let mut indices = Vec::new();
        visit_type(fallback_type, &mut |ty| {
            let Ty::TypeReference(reference) = ty else {
                return;
            };
            if !reference.type_arguments.is_empty() {
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

    fn candidate_substitutions(
        &mut self,
        arena: crate::types::CheckerArena<'a>,
    ) -> TypeParameterSubstitutions<'a> {
        let mut substitutions = TypeParameterSubstitutions::new();
        for index in 0..self.inferences.len() {
            if let Some(inferred_type) = self.get_inferred_type(index, arena) {
                substitutions.insert(self.inferences[index].type_parameter, inferred_type);
            }
        }
        substitutions
    }

    fn get_inferred_type(
        &mut self,
        index: usize,
        arena: crate::types::CheckerArena<'a>,
    ) -> Option<Ty<'a>> {
        if self.inferences[index].inferred_type.is_none() {
            let inference = &self.inferences[index];
            self.inferences[index].inferred_type =
                inferred_type_from_candidates(arena, inference, self.return_type);
        }
        self.inferences[index].inferred_type
    }
}

fn instantiate_inference_fallback_type<'a>(
    fallback_type: Ty<'a>,
    substitutions: &TypeParameterSubstitutions<'a>,
    arena: crate::types::CheckerArena<'a>,
) -> Ty<'a> {
    substitute_type(fallback_type, &substitutions.to_mapper(arena), arena)
}

fn inferred_type_from_candidates<'a>(
    arena: crate::types::CheckerArena<'a>,
    inference: &InferenceInfo<'a>,
    return_type: Option<Ty<'a>>,
) -> Option<Ty<'a>> {
    let covariant = resolve_covariant_candidates(arena, inference, return_type);
    let contravariant = resolve_contravariant_candidates(arena, inference);

    match (covariant, contravariant) {
        (Some(covariant), Some(contravariant)) => {
            if covariant.is_never() || covariant.is_any() {
                return Some(contravariant);
            }
            if inference
                .contra_candidates
                .iter()
                .any(|candidate| is_assignable_to_without_checker(covariant, *candidate))
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

fn resolve_covariant_candidates<'a>(
    arena: crate::types::CheckerArena<'a>,
    inference: &InferenceInfo<'a>,
    return_type: Option<Ty<'a>>,
) -> Option<Ty<'a>> {
    if inference.candidates.is_empty() {
        return None;
    }

    if return_type.is_none() {
        return Some(Ty::union(arena, inference.candidates.iter().copied()));
    }

    let candidates = if should_widen_literal_inference(inference, return_type) {
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
        Some(get_common_supertype(arena, &candidates))
    }
}

fn resolve_contravariant_candidates<'a>(
    arena: crate::types::CheckerArena<'a>,
    inference: &InferenceInfo<'a>,
) -> Option<Ty<'a>> {
    if inference.contra_candidates.is_empty() {
        return None;
    }

    if inference_priority_implies_combination(inference.priority) {
        Some(Ty::intersection(
            arena,
            inference.contra_candidates.iter().copied(),
        ))
    } else {
        Some(get_common_subtype(&inference.contra_candidates))
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
    inference: &InferenceInfo<'a>,
    return_type: Option<Ty<'a>>,
) -> bool {
    !has_primitive_constraint(inference.type_parameter)
        && inference.top_level
        && return_type.is_some_and(|return_type| {
            !is_type_parameter_at_top_level(return_type, inference.type_parameter, 0)
        })
}

fn has_primitive_constraint(type_parameter: TyTypeParameter<'_>) -> bool {
    type_parameter
        .constraint_type
        .is_some_and(type_maybe_contains_primitive_or_literal)
}

fn type_maybe_contains_primitive_or_literal(ty: Ty<'_>) -> bool {
    match ty {
        Ty::String
        | Ty::Number
        | Ty::Bigint
        | Ty::Boolean
        | Ty::Symbol
        | Ty::StringLiteral(_)
        | Ty::NumberLiteral(_)
        | Ty::BigIntLiteral(_)
        | Ty::BooleanLiteral(_)
        | Ty::UniqueSymbol(_)
        | Ty::Keyof(_)
        | Ty::TemplateLiteral(_) => true,
        Ty::Union(union) => union
            .types
            .iter()
            .any(|ty| type_maybe_contains_primitive_or_literal(*ty)),
        Ty::Intersection(intersection) => intersection
            .types
            .iter()
            .any(|ty| type_maybe_contains_primitive_or_literal(*ty)),
        Ty::Conditional(conditional) => {
            type_maybe_contains_primitive_or_literal(conditional.true_type)
                || type_maybe_contains_primitive_or_literal(conditional.false_type)
        }
        _ => false,
    }
}

fn is_type_parameter_at_top_level<'a>(
    ty: Ty<'a>,
    type_parameter: TyTypeParameter<'a>,
    depth: usize,
) -> bool {
    match ty {
        Ty::TypeReference(reference) => {
            reference.type_arguments.is_empty() && reference.name == type_parameter.name
        }
        Ty::Union(union) => union
            .types
            .iter()
            .any(|ty| is_type_parameter_at_top_level(*ty, type_parameter, depth)),
        Ty::Intersection(intersection) => intersection
            .types
            .iter()
            .any(|ty| is_type_parameter_at_top_level(*ty, type_parameter, depth)),
        Ty::Conditional(conditional) if depth < 3 => {
            is_type_parameter_at_top_level(conditional.true_type, type_parameter, depth + 1)
                || is_type_parameter_at_top_level(conditional.false_type, type_parameter, depth + 1)
        }
        _ => false,
    }
}

fn get_widened_literal_type<'a>(arena: crate::types::CheckerArena<'a>, ty: Ty<'a>) -> Ty<'a> {
    match ty {
        Ty::StringLiteral(_) | Ty::TemplateLiteral(_) => Ty::string(),
        Ty::NumberLiteral(_) => Ty::number(),
        Ty::BigIntLiteral(_) => Ty::bigint(),
        Ty::BooleanLiteral(_) => Ty::boolean(),
        Ty::Union(union) => Ty::union(
            arena,
            union
                .types
                .iter()
                .map(|ty| get_widened_literal_type(arena, *ty)),
        ),
        _ => ty,
    }
}

fn get_common_supertype<'a>(
    arena: crate::types::CheckerArena<'a>,
    candidates: &[Ty<'a>],
) -> Ty<'a> {
    if candidates.len() == 1 {
        return candidates[0];
    }
    if literal_types_with_same_base_type(candidates) {
        return Ty::union(arena, candidates.iter().copied());
    }

    get_single_common_supertype(candidates, is_assignable_to_without_checker)
}

fn get_single_common_supertype<'a>(
    candidates: &[Ty<'a>],
    is_subtype_of: impl Fn(Ty<'a>, Ty<'a>) -> bool,
) -> Ty<'a> {
    let candidate = find_leftmost_type(candidates, &is_subtype_of);
    if candidates
        .iter()
        .all(|ty| *ty == candidate || is_subtype_of(*ty, candidate))
    {
        return candidate;
    }
    find_leftmost_type(candidates, &is_assignable_to_without_checker)
}

fn get_common_subtype<'a>(candidates: &[Ty<'a>]) -> Ty<'a> {
    let mut subtype = candidates[0];
    for candidate in candidates.iter().skip(1) {
        if is_assignable_to_without_checker(*candidate, subtype) {
            subtype = *candidate;
        }
    }
    subtype
}

fn find_leftmost_type<'a>(
    candidates: &[Ty<'a>],
    is_left_subtype_of_right: &impl Fn(Ty<'a>, Ty<'a>) -> bool,
) -> Ty<'a> {
    let mut candidate = candidates[0];
    for ty in candidates.iter().skip(1) {
        if is_left_subtype_of_right(candidate, *ty) {
            candidate = *ty;
        }
    }
    candidate
}

fn literal_types_with_same_base_type(candidates: &[Ty<'_>]) -> bool {
    let mut common_base = None;
    for candidate in candidates {
        let Some(base) = literal_base_type(*candidate) else {
            return false;
        };
        if common_base.is_none() {
            common_base = Some(base);
        } else if common_base != Some(base) {
            return false;
        }
    }
    true
}

fn literal_base_type(ty: Ty<'_>) -> Option<Ty<'static>> {
    match ty {
        Ty::StringLiteral(_) => Some(Ty::String),
        Ty::NumberLiteral(_) => Some(Ty::Number),
        Ty::BigIntLiteral(_) => Some(Ty::Bigint),
        Ty::BooleanLiteral(_) => Some(Ty::Boolean),
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

impl<'a, 'store> CheckerReturn<'a, 'store> {
    pub(crate) fn infer_type_parameter_names(&self, ty: Ty<'a>) -> Vec<&'a str> {
        let mut names = Vec::new();
        self.collect_infer_type_parameter_names(ty, &mut names);
        names
    }

    fn collect_infer_type_parameter_names(&self, ty: Ty<'a>, names: &mut Vec<&'a str>) {
        visit_type(ty, &mut |ty| {
            if let Ty::Infer(infer) = ty
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
        CONDITIONAL_TYPE_DEPTH.with(|depth| {
            let current = depth.get();
            if current >= CONDITIONAL_TYPE_MAX_DEPTH {
                return Ty::Conditional(self.arena().alloc(TyConditional {
                    check_type,
                    extends_type,
                    true_type,
                    false_type,
                    is_distributive,
                }));
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
        })
    }

    fn conditional_type_inner(
        &self,
        check_type: Ty<'a>,
        extends_type: Ty<'a>,
        true_type: Ty<'a>,
        false_type: Ty<'a>,
        is_distributive: bool,
    ) -> Ty<'a> {
        if !self.infer_type_parameter_names(check_type).is_empty()
            || !self.infer_type_parameter_names(extends_type).is_empty()
        {
            let mut inferences = self.conditional_inference_context(check_type, extends_type);
            return match self.infer_conditional_from_types(
                check_type,
                extends_type,
                &mut inferences,
                0,
            ) {
                ConditionalInferMatchResult::Matched => {
                    let resolution = inferences.resolve_with_contextual_mapper(
                        self.arena(),
                        InferenceResolutionFlags::NONE,
                    );
                    self.instantiate_type(true_type, resolution.mapper())
                }
                ConditionalInferMatchResult::NoMatch => false_type,
                ConditionalInferMatchResult::Deferred => {
                    Ty::Conditional(self.arena().alloc(TyConditional {
                        check_type,
                        extends_type,
                        true_type,
                        false_type,
                        is_distributive,
                    }))
                }
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
        InferenceContext::with_substitutions(type_parameters, &TypeParameterSubstitutions::new())
    }

    fn add_conditional_inference(
        &self,
        inferences: &mut InferenceContext<'a>,
        infer: &TyInfer<'a>,
        candidate: Ty<'a>,
    ) -> ConditionalInferMatchResult {
        if let Some(constraint_type) = infer.type_parameter.constraint_type {
            let substitutions = inferences.candidate_substitutions(self.arena());
            let constraint_type =
                self.instantiate_type(constraint_type, &substitutions.to_mapper(self.arena()));
            if !self.infer_type_parameter_names(constraint_type).is_empty()
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
        if source == target && self.infer_type_parameter_names(target).is_empty() {
            return ConditionalInferMatchResult::Matched;
        }

        match (source, target) {
            (_, Ty::Infer(infer)) => self.add_conditional_inference(inferences, infer, source),
            (Ty::Any, target) if !self.infer_type_parameter_names(target).is_empty() => {
                let mut result = ConditionalInferMatchResult::Matched;
                self.collect_infer_types(target, &mut |infer| {
                    result =
                        result.and(self.add_conditional_inference(inferences, infer, Ty::any()));
                });
                result
            }
            (Ty::Object(source), Ty::Object(target)) => self.infer_conditional_from_properties(
                source.properties.iter().copied(),
                target.properties.iter().copied(),
                inferences,
                depth + 1,
            ),
            (Ty::Array(source), Ty::Array(target)) => self.infer_conditional_from_types(
                source.element_type,
                target.element_type,
                inferences,
                depth + 1,
            ),
            (Ty::Tuple(source), Ty::Tuple(target)) => self.infer_conditional_from_tuple_elements(
                &source.elements,
                &target.elements,
                inferences,
                depth + 1,
            ),
            (Ty::Function(source), Ty::Function(target)) => {
                self.infer_conditional_from_function_types(source, target, inferences, depth + 1)
            }
            (Ty::IndexedAccess(source), Ty::IndexedAccess(target)) => self
                .infer_conditional_from_type_pairs(
                    [
                        (source.object_type, target.object_type),
                        (source.index_type, target.index_type),
                    ],
                    inferences,
                    depth + 1,
                ),
            (Ty::TypeReference(source), Ty::TypeReference(target))
                if source.name == target.name
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
            (Ty::Union(source), Ty::Union(target)) if source.types.len() == target.types.len() => {
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
            (Ty::Union(source), target) => {
                let mut result = ConditionalInferMatchResult::Matched;
                for source_type in &source.types {
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
            (source, Ty::Union(target)) => {
                let mut deferred = false;
                for target_type in &target.types {
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
            _ => {
                if self.is_assignable_to(source, target) {
                    ConditionalInferMatchResult::Matched
                } else if self.could_contain_type_variables(source)
                    || self.could_contain_type_variables(target)
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
        visit_type(ty, &mut |ty| {
            if let Ty::Infer(infer) = ty {
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
    ) -> InferenceResolution<'a> {
        let argument_types = call_expression
            .arguments
            .iter()
            .enumerate()
            .filter_map(|(index, argument)| {
                let argument = argument.as_expression()?;
                let parameter_type = function_parameter_type_at_call_index(function, index)?;
                let flags = if self.could_contain_type_variables(parameter_type) {
                    GetTypeFlags::PRESERVE_LITERALS
                } else {
                    GetTypeFlags::NONE
                };
                let argument_type = self.get_type_of_call_argument_for_parameter(
                    program_id,
                    argument,
                    node_id,
                    parameter_type,
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
        let (substitutions, _) =
            self.explicit_type_parameter_substitutions(program_id, function, type_arguments);
        let mut context = InferenceContext::with_substitutions(
            function.type_parameters.iter().copied(),
            &substitutions,
        )
        .with_return_type(
            self.inference_return_type_for_literal_widening(program_id, function.return_type),
        );

        for (argument_index, argument_type) in argument_types {
            let Some(parameter_type) =
                function_parameter_type_at_call_index(function, argument_index)
            else {
                continue;
            };
            infer_types(parameter_type, argument_type, &mut context, self.arena());
        }

        context.resolve_with_contextual_mapper(self.arena(), InferenceResolutionFlags::NONE)
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
                return Ty::any();
            };
            let expressions = ReturnExpressionVisitor::expressions_in_body(body);
            if let FunctionKind::Function(f) = function
                && f.generator
            {
                // function*: look for yield expressions
                if expressions.yield_expressions.is_empty() {
                    return Ty::void();
                } else {
                    let flags = if expressions.yield_expressions.len() > 1 {
                        GetTypeFlags::PRESERVE_LITERALS
                    } else {
                        GetTypeFlags::NONE
                    };
                    Ty::union(
                        self.arena(),
                        expressions.yield_expressions.into_iter().map(|argument| {
                            self.get_type_of_expression_with_node(
                                program_id, argument, node_id, flags,
                            )
                        }),
                    )
                }
            } else {
                // non-generator function: look at return expressions
                if expressions.return_expressions.is_empty() {
                    Ty::void()
                } else {
                    let flags = if expressions.return_expressions.len() > 1 {
                        GetTypeFlags::PRESERVE_LITERALS
                    } else {
                        GetTypeFlags::NONE
                    };
                    Ty::union(
                        self.arena(),
                        expressions.return_expressions.into_iter().map(|argument| {
                            self.get_type_of_expression_with_node(
                                program_id, argument, node_id, flags,
                            )
                        }),
                    )
                }
            }
        };

        if function.returns_promise() {
            self.get_async_function_return_type(program_id, return_type)
        } else {
            return_type
        }
    }

    pub(crate) fn infer_construct_type_parameter_resolution(
        &self,
        program_id: ProgramId,
        function: &'a TyFunction<'a>,
        new_expression: &'a NewExpression<'a>,
    ) -> InferenceResolution<'a> {
        let (substitutions, _) = self.explicit_type_parameter_substitutions(
            program_id,
            function,
            new_expression.type_arguments.as_deref(),
        );
        let mut context = InferenceContext::with_substitutions(
            function.type_parameters.iter().copied(),
            &substitutions,
        )
        .with_return_type(
            self.inference_return_type_for_literal_widening(program_id, function.return_type),
        );

        for (argument, parameter) in new_expression
            .arguments
            .iter()
            .zip(function.parameters.iter())
        {
            let Some(argument) = argument.as_expression() else {
                continue;
            };
            let flags = if self.could_contain_type_variables(parameter.ty) {
                GetTypeFlags::PRESERVE_LITERALS
            } else {
                GetTypeFlags::NONE
            };
            let argument_type =
                self.get_type_of_expression_with_node(program_id, argument, None, flags);
            infer_types(parameter.ty, argument_type, &mut context, self.arena());
        }

        context.resolve_with_contextual_mapper(
            self.arena(),
            InferenceResolutionFlags::FILL_UNRESOLVED_WITH_UNKNOWN,
        )
    }

    fn inference_return_type_for_literal_widening(
        &self,
        program_id: ProgramId,
        return_type: Ty<'a>,
    ) -> Ty<'a> {
        match return_type {
            Ty::TypeReference(reference)
                if self.is_global_non_nullable_type_reference(program_id, reference) =>
            {
                reference.type_arguments[0]
            }
            Ty::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.inference_return_type_for_literal_widening(program_id, *ty)),
            ),
            Ty::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection
                    .types
                    .iter()
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

fn infer_type_pairs_with_variance<'a>(
    pairs: impl IntoIterator<Item = (Ty<'a>, Ty<'a>)>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    priority: InferencePriority,
    arena: crate::types::CheckerArena<'a>,
) {
    for (parameter_type, argument_type) in pairs {
        infer_types_with_variance(
            parameter_type,
            argument_type,
            context,
            variance,
            priority,
            arena,
        );
    }
}

fn infer_types<'a>(
    parameter_type: Ty<'a>,
    argument_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    arena: crate::types::CheckerArena<'a>,
) {
    infer_types_with_variance(
        parameter_type,
        argument_type,
        context,
        InferenceVariance::Covariant,
        InferencePriority::NakedTypeVariable,
        arena,
    );
}

fn infer_types_with_variance<'a>(
    parameter_type: Ty<'a>,
    argument_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    priority: InferencePriority,
    arena: crate::types::CheckerArena<'a>,
) {
    match (parameter_type, argument_type) {
        (Ty::Union(parameter_union), _) => {
            infer_type_parameter_from_union(
                parameter_union.types.iter().copied(),
                argument_type,
                context,
                variance,
                priority,
                arena,
            );
        }
        (Ty::Intersection(parameter_intersection), argument_type) => {
            infer_type_parameter_from_intersection(
                parameter_intersection.types.iter().copied(),
                argument_type,
                context,
                variance,
                priority,
                arena,
            );
        }
        (Ty::Array(parameter_array), Ty::Array(argument_array)) => {
            infer_types_with_variance(
                parameter_array.element_type,
                argument_array.element_type,
                context,
                variance,
                priority.structural(),
                arena,
            );
        }
        (Ty::Tuple(parameter_tuple), Ty::Tuple(argument_tuple)) => {
            infer_tuple_elements(
                &parameter_tuple.elements,
                &argument_tuple.elements,
                context,
                variance,
                priority.structural(),
                arena,
            );
        }
        (Ty::Keyof(parameter_keyof), Ty::Keyof(argument_keyof)) => {
            infer_types_with_variance(
                parameter_keyof.target,
                argument_keyof.target,
                context,
                variance,
                priority.structural(),
                arena,
            );
        }
        (Ty::IndexedAccess(parameter_indexed), Ty::IndexedAccess(argument_indexed)) => {
            infer_types_with_variance(
                parameter_indexed.object_type,
                argument_indexed.object_type,
                context,
                variance,
                priority.structural(),
                arena,
            );
            infer_types_with_variance(
                parameter_indexed.index_type,
                argument_indexed.index_type,
                context,
                variance,
                priority.structural(),
                arena,
            );
        }
        (Ty::IndexedAccess(parameter_indexed), argument_type) => {
            if let Some(simplified) = simplify_indexed_access_for_inference(
                parameter_indexed.object_type,
                parameter_indexed.index_type,
                context,
                arena,
            ) {
                infer_types_with_variance(
                    simplified,
                    argument_type,
                    context,
                    variance,
                    priority.structural(),
                    arena,
                );
            }
        }
        (Ty::Mapped(parameter_mapped), argument_type) => infer_to_mapped_type(
            parameter_mapped,
            argument_type,
            context,
            variance,
            priority,
            arena,
        ),
        (Ty::TypeReference(reference), _) if reference.type_arguments.is_empty() => {
            let Some(type_parameter) = context
                .inference_by_name_mut(reference.name)
                .map(|inference| inference.type_parameter)
            else {
                return;
            };
            match variance {
                InferenceVariance::Covariant => {
                    context.add_candidate(type_parameter, argument_type, priority)
                }
                InferenceVariance::Contravariant => {
                    context.add_contra_candidate(type_parameter, argument_type, priority)
                }
            }
        }
        (Ty::TypeReference(parameter_reference), Ty::TypeReference(argument_reference))
            if parameter_reference.name == argument_reference.name =>
        {
            infer_type_pairs_with_variance(
                parameter_reference
                    .type_arguments
                    .iter()
                    .copied()
                    .zip(argument_reference.type_arguments.iter().copied()),
                context,
                variance,
                priority.structural(),
                arena,
            );
        }
        (Ty::Object(parameter_object), Ty::Object(argument_object)) => {
            if let Some(pairs) = match_property_type_pairs(
                argument_object.properties.iter().copied(),
                parameter_object.properties.iter().copied(),
                PropertyMatchMode::ExistingOnly,
            ) {
                infer_type_pairs_with_variance(
                    pairs
                        .into_iter()
                        .map(|(argument, parameter)| (parameter, argument)),
                    context,
                    variance,
                    priority.structural(),
                    arena,
                );
            }
        }
        (Ty::Function(parameter_function), Ty::Function(argument_function)) => {
            infer_from_signature_types(
                parameter_function,
                argument_function,
                context,
                variance,
                priority,
                arena,
            );
        }
        _ => {}
    }
}

fn infer_from_signature_types<'a>(
    parameter_function: &TyFunction<'a>,
    argument_function: &TyFunction<'a>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    priority: InferencePriority,
    arena: crate::types::CheckerArena<'a>,
) {
    for (parameter, argument) in parameter_function
        .parameters
        .iter()
        .zip(argument_function.parameters.iter())
    {
        infer_types_with_variance(
            parameter.ty,
            argument.ty,
            context,
            variance.flip(),
            priority.structural(),
            arena,
        );
    }

    if type_contains_inference_variable(parameter_function.return_type, context) {
        infer_types_with_variance(
            parameter_function.return_type,
            argument_function.return_type,
            context,
            variance,
            priority.return_type(),
            arena,
        );
    }
}

fn type_contains_inference_variable<'a>(ty: Ty<'a>, context: &InferenceContext<'a>) -> bool {
    let mut contains = false;
    visit_type(ty, &mut |ty| {
        if let Ty::TypeReference(reference) = ty
            && reference.type_arguments.is_empty()
            && context.contains_type_parameter_name(reference.name)
        {
            contains = true;
        }
    });
    contains
}

fn infer_to_mapped_type<'a>(
    parameter_mapped: &TyMapped<'a>,
    argument_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    priority: InferencePriority,
    arena: crate::types::CheckerArena<'a>,
) {
    infer_to_mapped_type_with_constraint(
        parameter_mapped,
        parameter_mapped.constraint,
        argument_type,
        context,
        variance,
        priority,
        arena,
    );
}

fn simplify_indexed_access_for_inference<'a>(
    object_type: Ty<'a>,
    index_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    arena: crate::types::CheckerArena<'a>,
) -> Option<Ty<'a>> {
    let substitutions = context.candidate_substitutions(arena);
    let mapper = substitutions.to_mapper(arena);
    let object_type = substitute_type(object_type, &mapper, arena);
    let index_type = substitute_type(index_type, &mapper, arena);

    resolve_indexed_access_for_inference(object_type, index_type, arena)
}

fn resolve_indexed_access_for_inference<'a>(
    object_type: Ty<'a>,
    index_type: Ty<'a>,
    arena: crate::types::CheckerArena<'a>,
) -> Option<Ty<'a>> {
    if let Ty::Array(array) = object_type
        && index_type.is_number_index_type()
    {
        return Some(array.element_type);
    }

    if let Ty::Tuple(tuple) = object_type
        && let Some(index) = tuple_index_from_index_type(index_type)
    {
        return tuple.elements.get(index).map(TupleElement::ty);
    }

    match index_type {
        Ty::Union(union) => {
            let property_types = union
                .types
                .iter()
                .map(|index_type| {
                    resolve_indexed_access_for_inference(object_type, *index_type, arena)
                })
                .collect::<Option<Vec<_>>>()?;
            Some(Ty::union(arena, property_types))
        }
        _ => {
            let property_name = index_type_to_property_name(arena, index_type)?;
            property_type_for_inference_index(object_type, property_name, arena)
        }
    }
}

fn tuple_index_from_index_type(index_type: Ty<'_>) -> Option<usize> {
    match index_type {
        Ty::NumberLiteral(literal) => literal.to_usize(),
        _ => None,
    }
}

fn property_type_for_inference_index<'a>(
    object_type: Ty<'a>,
    property_name: &str,
    arena: crate::types::CheckerArena<'a>,
) -> Option<Ty<'a>> {
    match object_type {
        Ty::Object(object) => object.properties.iter().find_map(|property| {
            if property.computed || property.name != property_name {
                return None;
            }
            Some(if property.optional {
                Ty::union(arena, [property.ty, Ty::undefined()])
            } else {
                property.ty
            })
        }),
        Ty::Union(union) => {
            let property_types = union
                .types
                .iter()
                .map(|ty| property_type_for_inference_index(*ty, property_name, arena))
                .collect::<Option<Vec<_>>>()?;
            Some(Ty::union(arena, property_types))
        }
        Ty::Intersection(intersection) => intersection
            .types
            .iter()
            .find_map(|ty| property_type_for_inference_index(*ty, property_name, arena)),
        _ => None,
    }
}

fn infer_to_mapped_type_with_constraint<'a>(
    parameter_mapped: &TyMapped<'a>,
    constraint_type: Ty<'a>,
    argument_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    priority: InferencePriority,
    arena: crate::types::CheckerArena<'a>,
) {
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
    let Some(parameter_target) = same_shape_mapped_constraint_target(constraint_type) else {
        return infer_to_non_homomorphic_mapped_type(
            parameter_mapped,
            constraint_type,
            argument_type,
            context,
            variance,
            priority,
            arena,
        );
    };

    match argument_type {
        Ty::Mapped(argument_mapped) => {
            if let Some(argument_target) = same_shape_mapped_type_target(argument_mapped) {
                infer_types_with_variance(
                    parameter_target,
                    argument_target,
                    context,
                    variance,
                    InferencePriority::SameShapeMappedType,
                    arena,
                );
            } else {
                infer_types_with_variance(
                    parameter_mapped.constraint,
                    argument_mapped.constraint,
                    context,
                    variance,
                    priority.structural(),
                    arena,
                );
            }
        }
        Ty::Object(argument_object) => {
            infer_reverse_mapped_source_type(
                parameter_mapped,
                parameter_target,
                Ty::object(arena, argument_object.properties.iter().copied()),
                argument_object.properties.iter().copied(),
                context,
                variance,
                arena,
            );
        }
        Ty::Array(argument_array) => {
            let reverse_candidate = if argument_array.readonly {
                Ty::readonly_array(arena, argument_array.element_type)
            } else {
                Ty::array(arena, argument_array.element_type)
            };
            infer_reverse_mapped_source_type(
                parameter_mapped,
                parameter_target,
                reverse_candidate,
                [Ty::property("0", argument_array.element_type)],
                context,
                variance,
                arena,
            );
        }
        Ty::Tuple(argument_tuple) => {
            let elements = argument_tuple
                .elements
                .iter()
                .map(|element| reverse_mapped_tuple_element(*element, parameter_mapped, arena))
                .collect::<Vec<_>>();
            let reverse_candidate = if argument_tuple.readonly {
                Ty::readonly_tuple(arena, elements)
            } else {
                Ty::tuple(arena, elements)
            };
            let properties = argument_tuple
                .elements
                .iter()
                .enumerate()
                .map(|(index, element)| Ty::property(arena.str(&index.to_string()), element.ty()));
            infer_reverse_mapped_source_type(
                parameter_mapped,
                parameter_target,
                reverse_candidate,
                properties,
                context,
                variance,
                arena,
            );
        }
        _ => infer_types_with_variance(
            constraint_type,
            argument_type,
            context,
            variance,
            priority.structural(),
            arena,
        ),
    }
}

fn infer_to_non_homomorphic_mapped_type<'a>(
    parameter_mapped: &TyMapped<'a>,
    constraint_type: Ty<'a>,
    argument_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    priority: InferencePriority,
    arena: crate::types::CheckerArena<'a>,
) {
    match constraint_type {
        Ty::Union(union) => {
            for constraint in &union.types {
                infer_to_mapped_type_with_constraint(
                    parameter_mapped,
                    *constraint,
                    argument_type,
                    context,
                    variance,
                    priority,
                    arena,
                );
            }
        }
        Ty::Intersection(intersection) => {
            for constraint in &intersection.types {
                infer_to_mapped_type_with_constraint(
                    parameter_mapped,
                    *constraint,
                    argument_type,
                    context,
                    variance,
                    priority,
                    arena,
                );
            }
        }
        Ty::TypeReference(reference) if reference.type_arguments.is_empty() => {
            let key_type = Ty::keyof(arena, argument_type);
            infer_types_with_variance(
                constraint_type,
                key_type,
                context,
                variance,
                InferencePriority::MappedTypeConstraint,
                arena,
            );
            if let Some(extended_constraint) = context
                .type_parameter_by_name(reference.name)
                .and_then(|type_parameter| type_parameter.constraint_type)
            {
                infer_to_mapped_type_with_constraint(
                    parameter_mapped,
                    extended_constraint,
                    argument_type,
                    context,
                    variance,
                    priority,
                    arena,
                );
            } else if let Some(property_types) = inferable_property_types(argument_type) {
                infer_types_with_variance(
                    parameter_mapped.template,
                    Ty::union(arena, property_types),
                    context,
                    variance,
                    priority.structural(),
                    arena,
                );
            }
        }
        _ => infer_types_with_variance(
            constraint_type,
            argument_type,
            context,
            variance,
            priority.structural(),
            arena,
        ),
    }
}

fn infer_reverse_mapped_source_type<'a>(
    parameter_mapped: &TyMapped<'a>,
    parameter_target: Ty<'a>,
    reverse_candidate: Ty<'a>,
    argument_properties: impl IntoIterator<Item = TyProperty<'a>>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    arena: crate::types::CheckerArena<'a>,
) {
    let argument_properties = argument_properties.into_iter().collect::<Vec<_>>();

    infer_types_with_variance(
        parameter_target,
        reverse_candidate,
        context,
        variance,
        InferencePriority::SameShapeMappedType,
        arena,
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
        infer_types_with_variance(
            template_at_key,
            property.ty,
            context,
            variance,
            InferencePriority::SameShapeMappedType,
            arena,
        );
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

fn remove_undefined_from_type<'a>(ty: Ty<'a>, arena: crate::types::CheckerArena<'a>) -> Ty<'a> {
    let Ty::Union(union) = ty else {
        return ty;
    };
    let types = union
        .types
        .iter()
        .copied()
        .filter(|ty| !matches!(ty, Ty::Undefined))
        .collect::<Vec<_>>();
    if types.is_empty() {
        Ty::never()
    } else {
        Ty::union(arena, types)
    }
}

fn inferable_property_types<'a>(ty: Ty<'a>) -> Option<Vec<Ty<'a>>> {
    match ty {
        Ty::Object(object) => Some(
            object
                .properties
                .iter()
                .map(|property| property.ty)
                .collect(),
        ),
        Ty::Array(array) => Some(vec![array.element_type]),
        Ty::Tuple(tuple) => Some(tuple.elements.iter().map(TupleElement::ty).collect()),
        _ => None,
    }
}

fn substitute_type<'a>(
    ty: Ty<'a>,
    mapper: &TypeMapper<'a>,
    arena: crate::types::CheckerArena<'a>,
) -> Ty<'a> {
    match ty {
        Ty::TypeReference(reference) => {
            let mapped = mapper.map(ty);
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
        Ty::IndexedAccess(indexed_access) => Ty::indexed_access(
            arena,
            substitute_type(indexed_access.object_type, mapper, arena),
            substitute_type(indexed_access.index_type, mapper, arena),
        ),
        Ty::Keyof(keyof) => Ty::keyof(arena, substitute_type(keyof.target, mapper, arena)),
        Ty::Array(array) => Ty::array(arena, substitute_type(array.element_type, mapper, arena)),
        Ty::Tuple(tuple) => Ty::tuple(
            arena,
            tuple
                .elements
                .iter()
                .map(|element| match element {
                    TupleElement::Regular(ty) => {
                        TupleElement::Regular(substitute_type(*ty, mapper, arena))
                    }
                    TupleElement::Rest(ty) => {
                        TupleElement::Rest(substitute_type(*ty, mapper, arena))
                    }
                    TupleElement::Optional(ty) => {
                        TupleElement::Optional(substitute_type(*ty, mapper, arena))
                    }
                })
                .collect(),
        ),
        Ty::Union(union) => Ty::union(
            arena,
            union
                .types
                .iter()
                .map(|ty| substitute_type(*ty, mapper, arena)),
        ),
        Ty::Intersection(intersection) => Ty::intersection(
            arena,
            intersection
                .types
                .iter()
                .map(|ty| substitute_type(*ty, mapper, arena)),
        ),
        _ => mapper.map(ty),
    }
}

fn same_shape_mapped_type_target<'a>(mapped: &TyMapped<'a>) -> Option<Ty<'a>> {
    // In this checker's `TyMapped` representation, the TypeScript shape
    // `{ [P in keyof T]: ... }` is represented as `constraint = Ty::Keyof(T)`.
    // A key remapping clause (`as ...`) means the mapped type may no longer preserve
    // exactly the source key set, so keep those out of the same-shape bucket for now.
    if mapped.name_type.is_some() {
        return None;
    }
    same_shape_mapped_constraint_target(mapped.constraint)
}

fn same_shape_mapped_constraint_target<'a>(constraint: Ty<'a>) -> Option<Ty<'a>> {
    let Ty::Keyof(keyof) = constraint else {
        return None;
    };
    Some(keyof.target)
}

fn infer_tuple_elements<'a>(
    parameter_elements: &[TupleElement<'a>],
    argument_elements: &[TupleElement<'a>],
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    priority: InferencePriority,
    arena: crate::types::CheckerArena<'a>,
) {
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
            infer_types_with_variance(
                parameter.ty(),
                argument.ty(),
                context,
                variance,
                priority,
                arena,
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
        infer_types_with_variance(*rest_type, rest_tuple, context, variance, priority, arena);
        return;
    }

    if parameter_elements.len() != argument_elements.len() {
        return;
    }

    for (parameter, argument) in parameter_elements.iter().zip(argument_elements.iter()) {
        infer_types_with_variance(
            parameter.ty(),
            argument.ty(),
            context,
            variance,
            priority,
            arena,
        );
    }
}

fn infer_type_parameter_from_union<'a>(
    parameter_types: impl IntoIterator<Item = Ty<'a>>,
    argument_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    priority: InferencePriority,
    arena: crate::types::CheckerArena<'a>,
) {
    let parameter_types = parameter_types
        .into_iter()
        .filter(|ty| !matches!(ty, Ty::Null | Ty::Undefined | Ty::Never))
        .collect::<Vec<_>>();

    let candidates = select_union_inference_candidates(&parameter_types, argument_type, context);

    for candidate in candidates {
        infer_types_with_variance(candidate, argument_type, context, variance, priority, arena);
    }
}

fn select_union_inference_candidates<'a>(
    parameter_types: &[Ty<'a>],
    argument_type: Ty<'a>,
    context: &InferenceContext<'a>,
) -> Vec<Ty<'a>> {
    let structurally_matching = select_matching_union_constituents(parameter_types, argument_type);
    if !structurally_matching.is_empty() {
        return structurally_matching;
    }

    let naked_type_variables = select_naked_type_variable_constituents(parameter_types, context);
    if !naked_type_variables.is_empty() {
        return naked_type_variables;
    }

    parameter_types.to_vec()
}

fn select_matching_union_constituents<'a>(
    parameter_types: &[Ty<'a>],
    argument_type: Ty<'a>,
) -> Vec<Ty<'a>> {
    match argument_type {
        Ty::Function(_) => parameter_types
            .iter()
            .copied()
            .filter(|ty| matches!(ty, Ty::Function(_)))
            .collect(),
        Ty::TypeReference(argument_reference) => parameter_types
            .iter()
            .copied()
            .filter(|ty| {
                matches!(ty, Ty::TypeReference(parameter_reference) if parameter_reference.name == argument_reference.name)
            })
            .collect(),
        Ty::Array(_) => parameter_types
            .iter()
            .copied()
            .filter(|ty| matches!(ty, Ty::Array(_)))
            .collect(),
        Ty::Tuple(_) => parameter_types
            .iter()
            .copied()
            .filter(|ty| matches!(ty, Ty::Tuple(_)))
            .collect(),
        _ => Vec::new(),
    }
}

fn select_naked_type_variable_constituents<'a>(
    parameter_types: &[Ty<'a>],
    context: &InferenceContext<'a>,
) -> Vec<Ty<'a>> {
    parameter_types
        .iter()
        .copied()
        .filter(|ty| {
            matches!(ty, Ty::TypeReference(reference) if reference.type_arguments.is_empty() && context.contains_type_parameter_name(reference.name))
        })
        .collect()
}

fn infer_type_parameter_from_intersection<'a>(
    parameter_types: impl IntoIterator<Item = Ty<'a>>,
    argument_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    priority: InferencePriority,
    arena: crate::types::CheckerArena<'a>,
) {
    let parameter_types = parameter_types.into_iter().collect::<Vec<_>>();
    let argument_types = match argument_type {
        Ty::Intersection(intersection) => intersection.types.iter().copied().collect::<Vec<_>>(),
        _ => vec![argument_type],
    };

    let (unmatched_arguments, unmatched_parameters, removed_match) =
        remove_matching_intersection_constituents(argument_types, parameter_types);

    if !removed_match || unmatched_arguments.is_empty() || unmatched_parameters.is_empty() {
        return;
    }

    let argument_remainder = Ty::intersection(arena, unmatched_arguments);
    let parameter_remainder = Ty::intersection(arena, unmatched_parameters);
    infer_types_with_variance(
        parameter_remainder,
        argument_remainder,
        context,
        variance,
        priority.structural(),
        arena,
    );
}

fn remove_matching_intersection_constituents<'a>(
    mut source_types: Vec<Ty<'a>>,
    target_types: Vec<Ty<'a>>,
) -> (Vec<Ty<'a>>, Vec<Ty<'a>>, bool) {
    let mut unmatched_targets = Vec::new();
    let mut removed_match = false;

    for target in target_types {
        if let Some(index) = source_types.iter().position(|source| *source == target) {
            source_types.remove(index);
            removed_match = true;
        } else {
            unmatched_targets.push(target);
        }
    }

    (source_types, unmatched_targets, removed_match)
}

pub fn ts_signature_contains_infer(signature: &TSSignature<'_>) -> bool {
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

pub fn formal_parameters_contain_infer(parameters: &FormalParameters<'_>) -> bool {
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
mod tests {
    use oxc_allocator::Allocator;
    use oxc_ast::ast::NumberBase;

    use super::*;
    use crate::types::CheckerArena;

    #[test]
    fn resolves_dependent_default_when_only_dependent_parameter_is_read() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter_t = Ty::type_parameter("T", None, Some(Ty::string()));
        let type_parameter_u = Ty::type_parameter(
            "U",
            None,
            Some(Ty::type_reference(arena, "T", std::iter::empty())),
        );
        let mut context = InferenceContext::with_substitutions(
            [type_parameter_t, type_parameter_u],
            &TypeParameterSubstitutions::new(),
        );

        assert_eq!(
            context.resolve_type_parameter_by_name("U", arena, InferenceResolutionFlags::NONE,),
            Some(Ty::string()),
        );
        assert!(context.inferences[0].is_fixed);
        assert!(context.inferences[1].is_fixed);
    }

    #[test]
    fn resolving_type_parameter_fixes_it_before_dependent_default() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter_t = Ty::type_parameter("T", None, None);
        let type_parameter_u = Ty::type_parameter(
            "U",
            None,
            Some(Ty::type_reference(arena, "T", std::iter::empty())),
        );
        let mut context = InferenceContext::with_substitutions(
            [type_parameter_t, type_parameter_u],
            &TypeParameterSubstitutions::new(),
        );
        context.add_candidate(
            type_parameter_t,
            Ty::number(),
            InferencePriority::NakedTypeVariable,
        );

        assert_eq!(
            context.resolve_type_parameter_by_name("T", arena, InferenceResolutionFlags::NONE,),
            Some(Ty::number()),
        );
        assert!(context.inferences[0].is_fixed);
        assert_eq!(
            context.resolve_type_parameter_by_name("U", arena, InferenceResolutionFlags::NONE,),
            Some(Ty::number()),
        );
        assert!(context.inferences[1].is_fixed);
    }

    #[test]
    fn contextual_mapper_resolves_dependent_default_on_read() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter_t = Ty::type_parameter("T", None, Some(Ty::string()));
        let type_parameter_u = Ty::type_parameter(
            "U",
            None,
            Some(Ty::type_reference(arena, "T", std::iter::empty())),
        );
        let context = InferenceContext::with_substitutions(
            [type_parameter_t, type_parameter_u],
            &TypeParameterSubstitutions::new(),
        );
        let resolution =
            context.resolve_with_contextual_mapper(arena, InferenceResolutionFlags::NONE);

        assert_eq!(
            resolution
                .mapper()
                .map(Ty::type_reference(arena, "U", std::iter::empty())),
            Ty::string(),
        );
    }

    #[test]
    fn indexed_access_inference_simplifies_when_index_candidate_is_known() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter_t = Ty::type_parameter("T", None, None);
        let type_parameter_k =
            Ty::type_parameter("K", Some(Ty::string_literal(arena, "value")), None);
        let mut context = InferenceContext::with_substitutions(
            [type_parameter_t, type_parameter_k],
            &TypeParameterSubstitutions::new(),
        )
        .with_return_type(Ty::type_reference(arena, "T", std::iter::empty()));
        context.add_candidate(
            type_parameter_k,
            Ty::string_literal(arena, "value"),
            InferencePriority::NakedTypeVariable,
        );

        infer_types(
            Ty::indexed_access(
                arena,
                Ty::object(
                    arena,
                    [Ty::property(
                        "value",
                        Ty::type_reference(arena, "T", std::iter::empty()),
                    )],
                ),
                Ty::type_reference(arena, "K", std::iter::empty()),
            ),
            Ty::number(),
            &mut context,
            arena,
        );

        assert_eq!(
            context.resolve_type_parameter_by_name("T", arena, InferenceResolutionFlags::NONE),
            Some(Ty::number()),
        );
    }

    #[test]
    fn indexed_access_inference_preserves_unresolved_shape_without_index_candidate() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter_t = Ty::type_parameter("T", None, None);
        let type_parameter_k =
            Ty::type_parameter("K", Some(Ty::string_literal(arena, "value")), None);
        let mut context = InferenceContext::with_substitutions(
            [type_parameter_t, type_parameter_k],
            &TypeParameterSubstitutions::new(),
        )
        .with_return_type(Ty::type_reference(arena, "T", std::iter::empty()));

        infer_types(
            Ty::indexed_access(
                arena,
                Ty::object(
                    arena,
                    [Ty::property(
                        "value",
                        Ty::type_reference(arena, "T", std::iter::empty()),
                    )],
                ),
                Ty::type_reference(arena, "K", std::iter::empty()),
            ),
            Ty::number(),
            &mut context,
            arena,
        );

        assert_eq!(context.inferences[0].candidates, Vec::<Ty<'_>>::new());
    }

    #[test]
    fn covariant_candidates_use_common_supertype_without_combination_priority() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter = Ty::type_parameter("T", None, None);
        let mut context = InferenceContext::with_substitutions(
            [type_parameter],
            &TypeParameterSubstitutions::new(),
        )
        .with_return_type(Ty::type_reference(arena, "Result", std::iter::empty()));
        context.add_candidate(
            type_parameter,
            Ty::string_literal(arena, "ready"),
            InferencePriority::Low,
        );
        context.add_candidate(
            type_parameter,
            Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal),
            InferencePriority::Low,
        );

        assert_eq!(
            context.get_inferred_type(0, arena),
            Some(Ty::string_literal(arena, "ready"))
        );
    }

    #[test]
    fn covariant_candidates_combine_for_naked_type_variable_priority() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter = Ty::type_parameter("T", None, None);
        let mut context = InferenceContext::with_substitutions(
            [type_parameter],
            &TypeParameterSubstitutions::new(),
        );
        context.add_candidate(
            type_parameter,
            Ty::string_literal(arena, "ready"),
            InferencePriority::NakedTypeVariable,
        );
        context.add_candidate(
            type_parameter,
            Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal),
            InferencePriority::NakedTypeVariable,
        );

        assert_eq!(
            context.get_inferred_type(0, arena),
            Some(Ty::union(
                arena,
                [
                    Ty::string_literal(arena, "ready"),
                    Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal)
                ],
            )),
        );
    }

    #[test]
    fn top_level_literal_candidates_widen_when_not_top_level_in_return() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter = Ty::type_parameter("T", None, None);
        let mut context = InferenceContext::with_substitutions(
            [type_parameter],
            &TypeParameterSubstitutions::new(),
        )
        .with_return_type(Ty::object(
            arena,
            [Ty::property(
                "value",
                Ty::type_reference(arena, "T", std::iter::empty()),
            )],
        ));
        context.add_candidate(
            type_parameter,
            Ty::string_literal(arena, "ready"),
            InferencePriority::NakedTypeVariable,
        );

        assert_eq!(context.get_inferred_type(0, arena), Some(Ty::string()));
    }

    #[test]
    fn top_level_literal_candidates_are_preserved_for_top_level_return() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter = Ty::type_parameter("T", None, None);
        let mut context = InferenceContext::with_substitutions(
            [type_parameter],
            &TypeParameterSubstitutions::new(),
        )
        .with_return_type(Ty::type_reference(arena, "T", std::iter::empty()));
        context.add_candidate(
            type_parameter,
            Ty::string_literal(arena, "ready"),
            InferencePriority::NakedTypeVariable,
        );

        assert_eq!(
            context.get_inferred_type(0, arena),
            Some(Ty::string_literal(arena, "ready")),
        );
    }

    #[test]
    fn forward_default_references_resolve_to_unknown() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let type_parameter_t = Ty::type_parameter(
            "T",
            None,
            Some(Ty::type_reference(arena, "U", std::iter::empty())),
        );
        let type_parameter_u = Ty::type_parameter("U", None, None);
        let mut context = InferenceContext::with_substitutions(
            [type_parameter_t, type_parameter_u],
            &TypeParameterSubstitutions::new(),
        );

        assert_eq!(
            context.resolve_type_parameter_by_name("T", arena, InferenceResolutionFlags::NONE),
            Some(Ty::unknown()),
        );
        assert!(!context.inferences[1].is_fixed);
    }
}
