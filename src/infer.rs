use oxc_ast::ast::{
    ArrowFunctionExpression, CallExpression, Expression, FormalParameters, Function, FunctionBody,
    NewExpression, ReturnStatement, TSSignature, TSTupleElement, TSType,
};
use oxc_ast_visit::Visit;
use oxc_semantic::{NodeId, ScopeFlags};

use crate::{
    checker::{Checker, CheckerReturn},
    checker_impl::{FunctionKind, GetTypeFlags},
    mapper::{TypeMapper, TypeParameterSubstitutions},
    program::ProgramId,
    types::{
        TupleElement, Ty, TyConditional, TyFunction, TyInfer, TyMapped, TyProperty,
        TyTypeParameter, visit_type,
    },
};

const CONDITIONAL_INFER_MATCH_MAX_DEPTH: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ConditionalInferMatchResult {
    Matched,
    NoMatch,
    Deferred,
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
        let mapper = substitutions.to_mapper(arena);
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
        }
    }

    fn inference_by_name_mut(&mut self, name: &str) -> Option<&mut InferenceInfo<'a>> {
        self.inferences
            .iter_mut()
            .find(|inference| inference.type_parameter.name == name)
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
        mut instantiate_fallback: impl FnMut(Ty<'a>, &TypeParameterSubstitutions<'a>) -> Ty<'a>,
    ) -> InferenceResolution<'a> {
        let mut substitutions = TypeParameterSubstitutions::new();

        for index in 0..self.inferences.len() {
            let mut inferred_type = self.get_inferred_type(index, arena);

            if inferred_type.is_none()
                && let Some(fallback_type) = self.inferences[index]
                    .type_parameter
                    .default_type
                    .or(self.inferences[index].type_parameter.constraint_type)
            {
                let fallback_type = instantiate_fallback(fallback_type, &substitutions);
                self.inferences[index].inferred_type = Some(fallback_type);
                inferred_type = Some(fallback_type);
            }

            if inferred_type.is_none() && flags.fill_unresolved_with_unknown() {
                self.inferences[index].inferred_type = Some(Ty::unknown());
                inferred_type = Some(Ty::unknown());
            }

            if let Some(inferred_type) = inferred_type {
                substitutions.insert(self.inferences[index].type_parameter, inferred_type);
            }
        }
        InferenceResolution::new(substitutions, arena)
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
            self.inferences[index].inferred_type = inferred_type_from_candidates(
                arena,
                &self.inferences[index].candidates,
                &self.inferences[index].contra_candidates,
            );
        }
        self.inferences[index].inferred_type
    }
}

fn inferred_type_from_candidates<'a>(
    arena: crate::types::CheckerArena<'a>,
    candidates: &[Ty<'a>],
    contra_candidates: &[Ty<'a>],
) -> Option<Ty<'a>> {
    if !candidates.is_empty() {
        return Some(Ty::union(arena, candidates.iter().copied()));
    }
    if !contra_candidates.is_empty() {
        return Some(Ty::intersection(arena, contra_candidates.iter().copied()));
    }
    None
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
                    let resolution = inferences.resolve(
                        self.arena(),
                        InferenceResolutionFlags::NONE,
                        |fallback_type, substitutions| {
                            self.instantiate_type(
                                fallback_type,
                                &substitutions.to_mapper(self.arena()),
                            )
                        },
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
        let source_properties = source_properties.into_iter().collect::<Vec<_>>();
        let mut result = ConditionalInferMatchResult::Matched;
        for target_property in target_properties {
            let Some(source_property) = source_properties.iter().find(|source_property| {
                source_property.name == target_property.name
                    && source_property.computed == target_property.computed
            }) else {
                if target_property.optional {
                    continue;
                }
                return ConditionalInferMatchResult::NoMatch;
            };
            if source_property.optional && !target_property.optional {
                return ConditionalInferMatchResult::NoMatch;
            }
            result = result.and(self.infer_conditional_from_types(
                source_property.ty,
                target_property.ty,
                inferences,
                depth + 1,
            ));
            if result == ConditionalInferMatchResult::NoMatch {
                return result;
            }
        }
        result
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
        let (substitutions, _) = self.explicit_type_parameter_substitutions(
            program_id,
            function,
            call_expression.type_arguments.as_deref(),
        );
        let mut context = InferenceContext::with_substitutions(
            function.type_parameters.iter().copied(),
            &substitutions,
        );

        for (argument, parameter) in call_expression
            .arguments
            .iter()
            .zip(function.parameters.iter())
        {
            let Some(argument) = argument.as_expression() else {
                continue;
            };
            let argument_type = self.get_type_of_expression_with_node(
                program_id,
                argument,
                node_id,
                GetTypeFlags::NONE,
            );
            infer_types(parameter.ty, argument_type, &mut context, self.arena());
        }

        context.resolve(
            self.arena(),
            InferenceResolutionFlags::NONE,
            |fallback_type, substitutions| {
                self.instantiate_type(fallback_type, &substitutions.to_mapper(self.arena()))
            },
        )
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
            let return_expressions = ReturnExpressionVisitor::expressions_in_body(body);
            if return_expressions.is_empty() {
                Ty::void()
            } else {
                let flags = if return_expressions.len() > 1 {
                    GetTypeFlags::PRESERVE_LITERALS
                } else {
                    GetTypeFlags::NONE
                };
                Ty::union(
                    self.arena(),
                    return_expressions.into_iter().map(|argument| {
                        self.get_type_of_expression_with_node(program_id, argument, node_id, flags)
                    }),
                )
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
        );

        for (argument, parameter) in new_expression
            .arguments
            .iter()
            .zip(function.parameters.iter())
        {
            let Some(argument) = argument.as_expression() else {
                continue;
            };
            let argument_type = self.get_type_of_expression_with_node(
                program_id,
                argument,
                None,
                GetTypeFlags::NONE,
            );
            infer_types(parameter.ty, argument_type, &mut context, self.arena());
        }

        context.resolve(
            self.arena(),
            InferenceResolutionFlags::FILL_UNRESOLVED_WITH_UNKNOWN,
            |fallback_type, substitutions| {
                self.instantiate_type(fallback_type, &substitutions.to_mapper(self.arena()))
            },
        )
    }
}

struct ReturnExpressionVisitor<'a> {
    expressions: Vec<&'a Expression<'a>>,
}

impl<'a> ReturnExpressionVisitor<'a> {
    /// Collect return expressions from this function body, ignoring nested functions.
    fn expressions_in_body(body: &'a FunctionBody<'a>) -> Vec<&'a Expression<'a>> {
        let mut visitor = Self {
            expressions: Vec::new(),
        };
        visitor.visit_function_body(body);
        visitor.expressions
    }
}

impl<'a> Visit<'a> for ReturnExpressionVisitor<'a> {
    fn visit_return_statement(&mut self, statement: &ReturnStatement<'a>) {
        if let Some(argument) = statement.argument.as_ref() {
            self.expressions.push(self.alloc(argument));
        }
    }

    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(&mut self, _function: &ArrowFunctionExpression<'a>) {}
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
            for (parameter_type, argument_type) in parameter_reference
                .type_arguments
                .iter()
                .zip(argument_reference.type_arguments.iter())
            {
                infer_types_with_variance(
                    *parameter_type,
                    *argument_type,
                    context,
                    variance,
                    priority.structural(),
                    arena,
                );
            }
        }
        (Ty::Object(parameter_object), Ty::Object(argument_object)) => {
            for parameter_property in &parameter_object.properties {
                if let Some(argument_property) =
                    argument_object.properties.iter().find(|argument_property| {
                        argument_property.name == parameter_property.name
                            && argument_property.computed == parameter_property.computed
                    })
                {
                    infer_types_with_variance(
                        parameter_property.ty,
                        argument_property.ty,
                        context,
                        variance,
                        priority.structural(),
                        arena,
                    );
                }
            }
        }
        (Ty::Function(parameter_function), Ty::Function(argument_function)) => {
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
            infer_types_with_variance(
                parameter_function.return_type,
                argument_function.return_type,
                context,
                variance,
                priority.return_type(),
                arena,
            );
        }
        _ => {}
    }
}

fn infer_to_mapped_type<'a>(
    parameter_mapped: &TyMapped<'a>,
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
    let Some(parameter_target) = same_shape_mapped_type_target(parameter_mapped) else {
        return infer_types_with_variance(
            parameter_mapped.constraint,
            argument_type,
            context,
            variance,
            priority.structural(),
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
                argument_object.properties.iter().copied(),
                context,
                variance,
                arena,
            );
        }
        _ => infer_types_with_variance(
            parameter_mapped.constraint,
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
    argument_properties: impl IntoIterator<Item = TyProperty<'a>>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
    arena: crate::types::CheckerArena<'a>,
) {
    let argument_properties = argument_properties.into_iter().collect::<Vec<_>>();
    let reverse_candidate = Ty::object(arena, argument_properties.iter().copied());

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
    let Ty::Keyof(keyof) = mapped.constraint else {
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

    let candidates = match argument_type {
        Ty::Function(_) => parameter_types
            .iter()
            .copied()
            .filter(|ty| matches!(ty, Ty::Function(_)))
            .collect::<Vec<_>>(),
        Ty::TypeReference(argument_reference) => parameter_types
            .iter()
            .copied()
            .filter(|ty| {
                matches!(ty, Ty::TypeReference(parameter_reference) if parameter_reference.name == argument_reference.name)
            })
            .collect::<Vec<_>>(),
        _ => Vec::new(),
    };

    let candidates = if candidates.is_empty() {
        parameter_types
            .iter()
            .copied()
            .filter(|ty| {
                matches!(ty, Ty::TypeReference(reference) if reference.type_arguments.is_empty() && context.contains_type_parameter_name(reference.name))
            })
            .collect::<Vec<_>>()
    } else {
        candidates
    };

    let candidates = if candidates.is_empty() {
        parameter_types
    } else {
        candidates
    };

    for candidate in candidates {
        infer_types_with_variance(candidate, argument_type, context, variance, priority, arena);
    }
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
