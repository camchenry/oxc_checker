use oxc_ast::ast::{
    ArrowFunctionExpression, CallExpression, Expression, FormalParameters, Function, FunctionBody,
    NewExpression, ReturnStatement, TSSignature, TSTupleElement, TSType,
};
use oxc_ast_visit::Visit;
use oxc_semantic::{NodeId, ScopeFlags};

use crate::{
    checker::{Checker, CheckerReturn},
    checker_impl::{FunctionKind, GetTypeFlags, SubstituteTypeFlags},
    mapper::TypeParameterSubstitutions,
    program::ProgramId,
    types::{TupleElement, Ty, TyConditional, TyFunction, TyInfer, TyProperty, TyTypeParameter},
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

#[derive(Clone)]
struct ConditionalInferInferences<'a> {
    substitutions: TypeParameterSubstitutions<'a>,
}

impl ConditionalInferInferences<'_> {
    fn new() -> Self {
        Self {
            substitutions: TypeParameterSubstitutions::new(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum InferencePriority {
    None,
    NakedTypeVariable,
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

    pub(crate) fn into_substitutions(
        mut self,
        arena: crate::types::CheckerArena<'a>,
    ) -> TypeParameterSubstitutions<'a> {
        let mut substitutions = TypeParameterSubstitutions::new();
        for inference in &mut self.inferences {
            let inferred_type = inference.inferred_type.unwrap_or_else(|| {
                let inferred_type = inferred_type_from_candidates(
                    arena,
                    &inference.candidates,
                    &inference.contra_candidates,
                );
                inference.inferred_type = inferred_type;
                inferred_type.unwrap_or(Ty::any())
            });
            if inference.is_fixed
                || inference.top_level
                || !inference.candidates.is_empty()
                || !inference.contra_candidates.is_empty()
            {
                substitutions.insert(inference.type_parameter, inferred_type);
            }
        }
        substitutions
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
        match ty {
            Ty::Infer(infer) => {
                if !names.contains(&infer.type_parameter.name) {
                    names.push(infer.type_parameter.name);
                }
            }
            Ty::Object(object) => {
                for property in &object.properties {
                    self.collect_infer_type_parameter_names(property.ty, names);
                }
                for signature in &object.signatures {
                    self.collect_infer_type_parameter_names(
                        Ty::Function(signature.function),
                        names,
                    );
                }
            }
            Ty::ModuleNamespace(namespace) => {
                for property in &namespace.properties {
                    self.collect_infer_type_parameter_names(property.ty, names);
                }
            }
            Ty::Function(function) => {
                for type_parameter in &function.type_parameters {
                    if let Some(constraint_type) = type_parameter.constraint_type {
                        self.collect_infer_type_parameter_names(constraint_type, names);
                    }
                    if let Some(default_type) = type_parameter.default_type {
                        self.collect_infer_type_parameter_names(default_type, names);
                    }
                }
                for parameter in &function.parameters {
                    self.collect_infer_type_parameter_names(parameter.ty, names);
                }
                self.collect_infer_type_parameter_names(function.return_type, names);
                if let Some(target_type) = function
                    .type_predicate
                    .and_then(|predicate| predicate.target_type)
                {
                    self.collect_infer_type_parameter_names(target_type, names);
                }
            }
            Ty::TypeReference(reference) => {
                for ty in &reference.type_arguments {
                    self.collect_infer_type_parameter_names(*ty, names);
                }
            }
            Ty::TypeQuery(query) => {
                self.collect_infer_type_parameter_names(query.resolved, names);
                for ty in &query.type_arguments {
                    self.collect_infer_type_parameter_names(*ty, names);
                }
            }
            Ty::TemplateLiteral(template_literal) => {
                for ty in &template_literal.expressions {
                    self.collect_infer_type_parameter_names(*ty, names);
                }
            }
            Ty::Array(array) => self.collect_infer_type_parameter_names(array.element_type, names),
            Ty::Tuple(tuple) => {
                for element in &tuple.elements {
                    self.collect_infer_type_parameter_names(element.ty(), names);
                }
            }
            Ty::Union(union) => {
                for ty in &union.types {
                    self.collect_infer_type_parameter_names(*ty, names);
                }
            }
            Ty::Intersection(intersection) => {
                for ty in &intersection.types {
                    self.collect_infer_type_parameter_names(*ty, names);
                }
            }
            Ty::Keyof(keyof) => self.collect_infer_type_parameter_names(keyof.target, names),
            Ty::IndexedAccess(indexed_access) => {
                self.collect_infer_type_parameter_names(indexed_access.object_type, names);
                self.collect_infer_type_parameter_names(indexed_access.index_type, names);
            }
            Ty::Conditional(conditional) => {
                self.collect_infer_type_parameter_names(conditional.check_type, names);
                self.collect_infer_type_parameter_names(conditional.extends_type, names);
                self.collect_infer_type_parameter_names(conditional.true_type, names);
                self.collect_infer_type_parameter_names(conditional.false_type, names);
            }
            Ty::Mapped(mapped) => {
                self.collect_infer_type_parameter_names(mapped.constraint, names);
                if let Some(name_type) = mapped.name_type {
                    self.collect_infer_type_parameter_names(name_type, names);
                }
                self.collect_infer_type_parameter_names(mapped.template, names);
            }
            _ => {}
        }
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
            let mut inferences = ConditionalInferInferences::new();
            return match self.infer_conditional_from_types(
                check_type,
                extends_type,
                &mut inferences,
                0,
            ) {
                ConditionalInferMatchResult::Matched => self
                    .instantiate_type(true_type, &inferences.substitutions.to_mapper(self.arena())),
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

    fn add_conditional_inference(
        &self,
        inferences: &mut ConditionalInferInferences<'a>,
        infer: &TyInfer<'a>,
        candidate: Ty<'a>,
    ) -> ConditionalInferMatchResult {
        if let Some(constraint_type) = infer.type_parameter.constraint_type {
            let constraint_type = self.instantiate_type(
                constraint_type,
                &inferences.substitutions.to_mapper(self.arena()),
            );
            if !self.infer_type_parameter_names(constraint_type).is_empty()
                || self.could_contain_type_variables(constraint_type)
            {
                return ConditionalInferMatchResult::Deferred;
            }
            if !self.is_assignable_to(candidate, constraint_type) {
                return ConditionalInferMatchResult::NoMatch;
            }
        }

        match inferences.substitutions.get(infer.type_parameter) {
            Some(existing) if existing == candidate => ConditionalInferMatchResult::Matched,
            Some(existing) => {
                inferences.substitutions.insert(
                    infer.type_parameter,
                    Ty::union(self.arena(), [existing, candidate]),
                );
                ConditionalInferMatchResult::Matched
            }
            None => {
                inferences
                    .substitutions
                    .insert(infer.type_parameter, candidate);
                ConditionalInferMatchResult::Matched
            }
        }
    }

    fn infer_conditional_from_types(
        &self,
        source: Ty<'a>,
        target: Ty<'a>,
        inferences: &mut ConditionalInferInferences<'a>,
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
        inferences: &mut ConditionalInferInferences<'a>,
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
        inferences: &mut ConditionalInferInferences<'a>,
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
        inferences: &mut ConditionalInferInferences<'a>,
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
        match ty {
            Ty::Infer(infer) => f(infer),
            Ty::Object(object) => {
                for property in &object.properties {
                    self.collect_infer_types(property.ty, f);
                }
                for signature in &object.signatures {
                    self.collect_infer_types(Ty::Function(signature.function), f);
                }
            }
            Ty::ModuleNamespace(namespace) => {
                for property in &namespace.properties {
                    self.collect_infer_types(property.ty, f);
                }
            }
            Ty::Function(function) => {
                for type_parameter in &function.type_parameters {
                    if let Some(constraint_type) = type_parameter.constraint_type {
                        self.collect_infer_types(constraint_type, f);
                    }
                    if let Some(default_type) = type_parameter.default_type {
                        self.collect_infer_types(default_type, f);
                    }
                }
                for parameter in &function.parameters {
                    self.collect_infer_types(parameter.ty, f);
                }
                self.collect_infer_types(function.return_type, f);
                if let Some(target_type) = function
                    .type_predicate
                    .and_then(|predicate| predicate.target_type)
                {
                    self.collect_infer_types(target_type, f);
                }
            }
            Ty::TypeReference(reference) => {
                for ty in &reference.type_arguments {
                    self.collect_infer_types(*ty, f);
                }
            }
            Ty::TypeQuery(query) => {
                self.collect_infer_types(query.resolved, f);
                for ty in &query.type_arguments {
                    self.collect_infer_types(*ty, f);
                }
            }
            Ty::TemplateLiteral(template_literal) => {
                for ty in &template_literal.expressions {
                    self.collect_infer_types(*ty, f);
                }
            }
            Ty::Array(array) => self.collect_infer_types(array.element_type, f),
            Ty::Tuple(tuple) => {
                for element in &tuple.elements {
                    self.collect_infer_types(element.ty(), f);
                }
            }
            Ty::Union(union) => {
                for ty in &union.types {
                    self.collect_infer_types(*ty, f);
                }
            }
            Ty::Intersection(intersection) => {
                for ty in &intersection.types {
                    self.collect_infer_types(*ty, f);
                }
            }
            Ty::Keyof(keyof) => self.collect_infer_types(keyof.target, f),
            Ty::IndexedAccess(indexed_access) => {
                self.collect_infer_types(indexed_access.object_type, f);
                self.collect_infer_types(indexed_access.index_type, f);
            }
            Ty::Conditional(conditional) => {
                self.collect_infer_types(conditional.check_type, f);
                self.collect_infer_types(conditional.extends_type, f);
                self.collect_infer_types(conditional.true_type, f);
                self.collect_infer_types(conditional.false_type, f);
            }
            Ty::Mapped(mapped) => {
                self.collect_infer_types(mapped.constraint, f);
                if let Some(name_type) = mapped.name_type {
                    self.collect_infer_types(name_type, f);
                }
                self.collect_infer_types(mapped.template, f);
            }
            _ => {}
        }
    }

    pub(crate) fn infer_call_type_parameter_substitutions(
        &self,
        program_id: ProgramId,
        function: &'a TyFunction<'a>,
        call_expression: &'a CallExpression<'a>,
        node_id: Option<NodeId>,
    ) -> TypeParameterSubstitutions<'a> {
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
            infer_types(parameter.ty, argument_type, &mut context);
        }

        let mut substitutions = context.into_substitutions(self.arena());
        self.add_type_parameter_fallback_substitutions(
            function,
            &mut substitutions,
            SubstituteTypeFlags::NONE,
        );

        substitutions
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

    pub(crate) fn infer_construct_type_parameter_substitutions(
        &self,
        program_id: ProgramId,
        function: &'a TyFunction<'a>,
        new_expression: &'a NewExpression<'a>,
    ) -> TypeParameterSubstitutions<'a> {
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
            infer_types(parameter.ty, argument_type, &mut context);
        }

        let mut substitutions = context.into_substitutions(self.arena());
        self.add_type_parameter_fallback_substitutions(
            function,
            &mut substitutions,
            SubstituteTypeFlags::FILL_UNRESOLVED_WITH_UNKNOWN,
        );

        substitutions
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
) {
    infer_types_with_variance(
        parameter_type,
        argument_type,
        context,
        InferenceVariance::Covariant,
    );
}

fn infer_types_with_variance<'a>(
    parameter_type: Ty<'a>,
    argument_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
) {
    match (parameter_type, argument_type) {
        (Ty::Union(parameter_union), _) => {
            infer_type_parameter_from_union(
                parameter_union.types.iter().copied(),
                argument_type,
                context,
                variance,
            );
        }
        (Ty::TypeReference(reference), _) if reference.type_arguments.is_empty() => {
            let Some(type_parameter) = context
                .inference_by_name_mut(reference.name)
                .map(|inference| inference.type_parameter)
            else {
                return;
            };
            match variance {
                InferenceVariance::Covariant => context.add_candidate(
                    type_parameter,
                    argument_type,
                    InferencePriority::NakedTypeVariable,
                ),
                InferenceVariance::Contravariant => context.add_contra_candidate(
                    type_parameter,
                    argument_type,
                    InferencePriority::NakedTypeVariable,
                ),
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
                infer_types_with_variance(*parameter_type, *argument_type, context, variance);
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
                infer_types_with_variance(parameter.ty, argument.ty, context, variance.flip());
            }
            infer_types_with_variance(
                parameter_function.return_type,
                argument_function.return_type,
                context,
                variance,
            );
        }
        _ => {}
    }
}

fn infer_type_parameter_from_union<'a>(
    parameter_types: impl IntoIterator<Item = Ty<'a>>,
    argument_type: Ty<'a>,
    context: &mut InferenceContext<'a>,
    variance: InferenceVariance,
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
        infer_types_with_variance(candidate, argument_type, context, variance);
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
