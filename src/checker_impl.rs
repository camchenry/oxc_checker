use bitflags::bitflags;
use oxc_ast::{
    AstKind,
    ast::{
        ArrayExpression, ArrayExpressionElement, ArrowFunctionExpression, AssignmentExpression,
        AssignmentTarget, AwaitExpression, BigIntLiteral, BinaryExpression, BindingPattern,
        CallExpression, ChainElement, Class, ClassElement, ComputedMemberExpression,
        ConditionalExpression, ExportSpecifier, Expression, FormalParameter, FormalParameterRest,
        FormalParameters, Function, IdentifierReference, ImportExpression, LogicalExpression,
        MethodDefinition, MethodDefinitionKind, ModuleExportName, NewExpression, NumberBase,
        ObjectExpression, ObjectPropertyKind, PrivateFieldExpression, PropertyDefinition,
        PropertyKey, SimpleAssignmentTarget, StaticMemberExpression, StringLiteral, TSImportType,
        TSImportTypeQualifier, TSInterfaceDeclaration, TSLiteral, TSMappedType, TSMethodSignature,
        TSMethodSignatureKind, TSModuleDeclarationName, TSNamedTupleMember, TSSignature,
        TSThisParameter, TSTupleElement, TSType, TSTypeAnnotation, TSTypeName,
        TSTypeOperatorOperator, TSTypeParameter, TSTypeParameterDeclaration,
        TSTypeParameterInstantiation, TSTypeQuery, TSTypeQueryExprName, TSTypeReference,
        TaggedTemplateExpression, TemplateLiteral, VariableDeclarationKind, VariableDeclarator,
        YieldExpression,
    },
};
use oxc_index::IndexVec;
use oxc_semantic::{AstNodes, NodeId, Semantic, SymbolId};
use oxc_span::{GetSpan, Span};
use oxc_str::{Ident, static_ident};
use oxc_syntax::{
    module_record::{ExportExportName, ExportLocalName},
    operator::{AssignmentOperator, BinaryOperator, LogicalOperator, UnaryOperator},
};
use std::collections::{HashMap, HashSet};

use crate::{
    TemplateLiteralElement, binding_pattern_default_initializer_symbol_id,
    checker::{
        Checker, CheckerReturn, ClassMemberResolution, InstantiationCacheKey, NodeRef, SymbolRef,
        TypeAliasMetadata, TypeAliasResolution, TypeParameterResolution, TypeStringCacheKey,
        TypeStringContext,
    },
    evolving_arrays, flow, for_statement_left_contains_declarator, index_signature_key_types,
    index_type_to_property_name,
    infer::{InferenceResolution, ts_type_contains_infer},
    is_empty_object_intersection, is_mapped_empty_object_intersection,
    is_promise_like_type_reference,
    limits::{
        TS_TYPE_RESOLUTION_MAX_DEPTH, TYPE_EXPANSION_MAX_DEPTH, TYPE_INSTANTIATION_MAX_DEPTH,
    },
    mapper::{TypeMapper, TypeParameterSubstitutions},
    program::{self, ProgramId},
    property_key_name_str, push_type_parameter_names, string_literal_type_to_property_name,
    ts_type_name_to_str, ts_type_query_expr_name_to_str, tuple_element_type_at_index,
    tuple_index_from_expression, tuple_index_from_index_type, type_facts,
    types::{
        CheckerArena, IndexInfo, MappedModifier, Signature, SignatureKind, TupleElement, Ty,
        TyConditional, TyFunction, TyMapped, TyObject, TyParameter, TyProperty, TyTypeParameter,
        TyTypePredicate, TyTypeQuery, TyTypeReference, TypeData, TypeErrorKind, TypeId,
        binding_pattern_to_parameter_name, function_maximum_argument_count,
        function_minimum_argument_count, function_parameter_type_at_call_index,
        return_type_and_type_predicate_from_annotation_with_resolver, type_predicate_return_type,
        visit_type,
    },
};

fn should_display_implicit_default_type_argument<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> bool {
    !matches!(
        arena.type_data(ty),
        TypeData::Any | TypeData::Error(_) | TypeData::Unknown
    )
}

fn array_expression_element_span(element: &ArrayExpressionElement<'_>) -> Option<Span> {
    match element {
        ArrayExpressionElement::SpreadElement(spread) => Some(spread.argument.span()),
        ArrayExpressionElement::Elision(_) => None,
        _ => Some(element.to_expression().span()),
    }
}

fn capitalize_first_character(value: &str, uppercase: bool) -> String {
    let Some(first) = value.chars().next() else {
        return String::new();
    };
    let first_len = first.len_utf8();
    let mut mapped = if uppercase {
        first.to_uppercase().collect::<String>()
    } else {
        first.to_lowercase().collect::<String>()
    };
    mapped.push_str(&value[first_len..]);
    mapped
}

pub const UNDEFINED_IDENT: Ident = static_ident!("undefined");

const GLOBAL_THIS_IDENT: Ident = static_ident!("globalThis");
const SYMBOL_ITERATOR_PROPERTY_NAME: &str = "Symbol.iterator";
const SYMBOL_ASYNC_ITERATOR_PROPERTY_NAME: &str = "Symbol.asyncIterator";

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum IterationResolverKind {
    Sync,
    Async,
}

impl IterationResolverKind {
    fn property_name(self) -> &'static str {
        match self {
            Self::Sync => SYMBOL_ITERATOR_PROPERTY_NAME,
            Self::Async => SYMBOL_ASYNC_ITERATOR_PROPERTY_NAME,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum IterationInterfaceResolutionKind {
    IterableProperty,
    Iterator,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct IterationInterfaceResolution {
    kind: IterationInterfaceResolutionKind,
    resolver: IterationResolverKind,
    symbol: SymbolRef,
    type_arguments: Vec<TypeId>,
}

impl IterationInterfaceResolution {
    fn new(
        kind: IterationInterfaceResolutionKind,
        resolver: IterationResolverKind,
        symbol: SymbolRef,
        reference: &TyTypeReference<'_>,
    ) -> Self {
        Self {
            kind,
            resolver,
            symbol,
            type_arguments: reference.type_arguments.iter().map(|ty| ty.id()).collect(),
        }
    }
}

#[derive(Default)]
struct IterationResolutionContext {
    active_interfaces: HashSet<IterationInterfaceResolution>,
}

#[derive(Clone, Copy, Debug, Default)]
struct IterationTypes<'a> {
    yield_type: Option<Ty<'a>>,
    return_type: Option<Ty<'a>>,
    next_type: Option<Ty<'a>>,
}

impl IterationTypes<'_> {
    fn has_types(self) -> bool {
        self.yield_type.is_some() || self.return_type.is_some() || self.next_type.is_some()
    }
}

#[derive(Clone, Copy, Debug)]
struct IteratorResultStates {
    can_yield: bool,
    can_return: bool,
}

impl IteratorResultStates {
    fn union(self, other: Self) -> Self {
        Self {
            can_yield: self.can_yield || other.can_yield,
            can_return: self.can_return || other.can_return,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum FunctionKind<'a> {
    Function(&'a Function<'a>),
    ArrowFunction(&'a ArrowFunctionExpression<'a>),
}

impl<'a> FunctionKind<'a> {
    pub(crate) fn returns_promise(self) -> bool {
        match self {
            FunctionKind::Function(function) => function.r#async && !function.generator,
            FunctionKind::ArrowFunction(function) => function.r#async,
        }
    }

    pub(crate) fn annotated_return_type(self) -> Option<&'a TSTypeAnnotation<'a>> {
        match self {
            FunctionKind::Function(function) => function.return_type.as_deref(),
            FunctionKind::ArrowFunction(function) => function.return_type.as_deref(),
        }
    }

    pub(crate) fn parameters(self) -> &'a FormalParameters<'a> {
        match self {
            FunctionKind::Function(function) => &function.params,
            FunctionKind::ArrowFunction(function) => &function.params,
        }
    }

    pub(crate) fn type_parameters(self) -> Option<&'a TSTypeParameterDeclaration<'a>> {
        match self {
            FunctionKind::Function(function) => function.type_parameters.as_deref(),
            FunctionKind::ArrowFunction(function) => function.type_parameters.as_deref(),
        }
    }
}

impl<'a> GetSpan for FunctionKind<'a> {
    fn span(&self) -> Span {
        match self {
            FunctionKind::Function(function) => function.span,
            FunctionKind::ArrowFunction(function) => function.span,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum CallKind<'a> {
    Call(&'a CallExpression<'a>),
    New(&'a NewExpression<'a>),
}

impl<'a> CallKind<'a> {
    pub(crate) fn type_arguments(self) -> Option<&'a TSTypeParameterInstantiation<'a>> {
        match self {
            CallKind::Call(call_expression) => call_expression.type_arguments.as_deref(),
            CallKind::New(new_expression) => new_expression.type_arguments.as_deref(),
        }
    }
}

struct ResolvedSignatureCandidate<'a> {
    signature: Signature<'a>,
    inference: InferenceResolution<'a>,
    return_type: Ty<'a>,
}

impl<'a> ResolvedSignatureCandidate<'a> {
    fn into_return_type(self) -> Ty<'a> {
        let Self {
            signature,
            inference,
            return_type,
        } = self;
        let _ = signature.kind;
        let _ = inference.mapper().is_empty();
        return_type
    }
}

#[derive(Debug, Clone, Copy)]
enum IndexedAccessResolution<'a> {
    Resolved(Ty<'a>),
    Deferred,
    Missing,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum BindingPatternKind<'a> {
    FormalParameter(&'a FormalParameter<'a>),
    VariableDeclarator(&'a VariableDeclarator<'a>),
    RestParameter(&'a FormalParameterRest<'a>),
}

// TODO: Consolidate this with `CheckMode`?
bitflags! {
    /// Flags for changing behavior when getting the types of expressions or nodes.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) struct GetTypeFlags: u8 {
        const NONE = 0;
        /// Indicates that when literals are encountered, they should be preserved instead of widened
        /// to a more general type. For example: prefer `123` over `number`, `"foo"` over `string`.
        const PRESERVE_LITERALS = 1 << 0;
        /// Indicates expression typing should avoid flow-sensitive/contextual recursive queries.
        const CONTEXT_FREE = 1 << 1;
    }
}

impl GetTypeFlags {
    pub fn preserve_literals(&self) -> bool {
        self.contains(GetTypeFlags::PRESERVE_LITERALS)
    }

    pub fn context_free(&self) -> bool {
        self.contains(GetTypeFlags::CONTEXT_FREE)
    }
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct CheckMode: u8 {
        const NONE = 0;
        const CONTEXTUAL = 1 << 0;
        const FORCE_TUPLE = 1 << 1;
        const CONST_CONTEXT = 1 << 2;
    }
}

impl CheckMode {
    fn force_tuple(self) -> bool {
        self.contains(Self::FORCE_TUPLE)
    }

    fn const_context(self) -> bool {
        self.contains(Self::CONST_CONTEXT)
    }
}

#[derive(Debug, Clone, Copy)]
struct ExpressionCheckContext<'a> {
    flags: GetTypeFlags,
    contextual_type: Option<Ty<'a>>,
    check_mode: CheckMode,
}

impl<'a> ExpressionCheckContext<'a> {
    fn new(flags: GetTypeFlags) -> Self {
        Self {
            flags,
            contextual_type: None,
            check_mode: CheckMode::NONE,
        }
    }

    fn with_flags(self, flags: GetTypeFlags) -> Self {
        Self { flags, ..self }
    }

    fn with_contextual_type(self, contextual_type: Ty<'a>, check_mode: CheckMode) -> Self {
        Self {
            contextual_type: Some(contextual_type),
            check_mode: self.check_mode | check_mode,
            ..self
        }
    }

    fn with_check_mode(self, check_mode: CheckMode) -> Self {
        Self {
            check_mode: self.check_mode | check_mode,
            ..self
        }
    }
}

bitflags! {
    /// Flags for changing behavior when substituting type parameters.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) struct SubstituteTypeFlags: u8 {
        const NONE = 0;
        /// Indicates that when substituting type parameters, unresolved type parameters should be filled with `unknown`.
        const FILL_UNRESOLVED_WITH_UNKNOWN = 1 << 0;
    }
}

impl SubstituteTypeFlags {
    /// Whether to fill unresolved type parameters with `unknown`.
    pub fn fill_unresolved_with_unknown(&self) -> bool {
        self.contains(SubstituteTypeFlags::FILL_UNRESOLVED_WITH_UNKNOWN)
    }
}

impl<'a, 'store> CheckerReturn<'a, 'store> {
    #[inline]
    pub fn entry(&self, program_id: ProgramId) -> &program::ProgramEntry<'a> {
        self.store
            .entry(program_id)
            .expect("store-backed checker must reference a valid program")
    }

    #[inline]
    pub fn semantic(&self, program_id: ProgramId) -> &Semantic<'a> {
        self.entry(program_id).semantic()
    }

    #[inline]
    pub fn nodes(&self, program_id: ProgramId) -> &AstNodes<'a> {
        self.semantic(program_id).nodes()
    }

    #[inline]
    pub fn node_kind(&self, node: NodeRef) -> AstKind<'a> {
        self.nodes(node.program_id).kind(node.node_id)
    }

    #[inline]
    pub fn arena(&self) -> CheckerArena<'a> {
        self.arena
    }

    #[inline]
    pub(crate) fn instantiate_type(&self, ty: Ty<'a>, mapper: &TypeMapper<'a>) -> Ty<'a> {
        if mapper.is_empty() || !self.could_contain_type_variables(ty) {
            return ty;
        }

        let depth = &self.type_instantiation_depth;
        let current = depth.get();
        if current >= TYPE_INSTANTIATION_MAX_DEPTH {
            self.mark_type_instantiation_overflow();
            return Ty::error(self.arena(), TypeErrorKind::TypeInstantiationDepthExceeded);
        }

        depth.set(current + 1);
        let instantiated = self.instantiate_type_cached(ty, mapper);
        depth.set(current);
        instantiated
    }

    fn instantiate_type_cached(&self, ty: Ty<'a>, mapper: &TypeMapper<'a>) -> Ty<'a> {
        let Some(mapper_key) = mapper.cache_entries(self.arena()) else {
            return self.instantiate_type_at_depth(ty, mapper, 0);
        };
        let key = InstantiationCacheKey {
            target: ty.id(),
            mapper: mapper_key,
        };
        if let Some(instantiated) = self.instantiation_cache.borrow().get(&key) {
            return *instantiated;
        }
        let instantiated = self.instantiate_type_at_depth(ty, mapper, 0);
        self.instantiation_cache
            .borrow_mut()
            .insert(key, instantiated);
        instantiated
    }

    fn instantiate_type_at_depth(
        &self,
        ty: Ty<'a>,
        mapper: &TypeMapper<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_INSTANTIATION_MAX_DEPTH {
            return Ty::error(self.arena(), TypeErrorKind::TypeInstantiationDepthExceeded);
        }
        if mapper.is_empty() || !self.could_contain_type_variables(ty) {
            return ty;
        }

        self.instantiate_type_worker(ty, mapper, depth + 1)
    }

    #[inline]
    pub(crate) fn instantiate_signature(
        &self,
        signature: Signature<'a>,
        mapper: &TypeMapper<'a>,
    ) -> Signature<'a> {
        self.instantiate_signature_at_depth(signature, mapper, 0)
    }

    fn instantiate_signature_at_depth(
        &self,
        signature: Signature<'a>,
        mapper: &TypeMapper<'a>,
        depth: usize,
    ) -> Signature<'a> {
        let ty = self.instantiate_type_at_depth(signature.ty, mapper, depth);
        let TypeData::Function(_) = self.arena().type_data(ty) else {
            unreachable!("signature instantiation preserves function type")
        };
        Signature::new(signature.kind, ty)
    }

    #[inline]
    pub(crate) fn instantiate_type_predicate(
        &self,
        predicate: TyTypePredicate<'a>,
        mapper: &TypeMapper<'a>,
    ) -> TyTypePredicate<'a> {
        self.instantiate_type_predicate_at_depth(predicate, mapper, 0)
    }

    fn instantiate_type_predicate_at_depth(
        &self,
        predicate: TyTypePredicate<'a>,
        mapper: &TypeMapper<'a>,
        depth: usize,
    ) -> TyTypePredicate<'a> {
        TyTypePredicate {
            kind: predicate.kind,
            parameter_name: predicate.parameter_name,
            parameter_index: predicate.parameter_index,
            target_type: predicate
                .target_type
                .map(|ty| self.instantiate_type_at_depth(ty, mapper, depth + 1)),
        }
    }

    fn instantiate_type_worker(&self, ty: Ty<'a>, mapper: &TypeMapper<'a>, depth: usize) -> Ty<'a> {
        match self.arena().type_data(ty) {
            TypeData::Object(object) => {
                let instantiated = Ty::object(
                    self.arena(),
                    object.properties.iter().map(|property| TyProperty {
                        name: property.name,
                        computed: property.computed,
                        optional: property.optional,
                        method: property.method,
                        readonly: property.readonly,
                        ty: self.instantiate_type_at_depth(property.ty, mapper, depth + 1),
                    }),
                )
                .with_index_infos(
                    self.arena(),
                    object.index_infos.iter().map(|info| {
                        IndexInfo::new(
                            info.name,
                            self.instantiate_type_at_depth(info.key_type, mapper, depth + 1),
                            self.instantiate_type_at_depth(info.value_type, mapper, depth + 1),
                            info.readonly,
                        )
                    }),
                )
                .with_signatures(
                    self.arena(),
                    object.signatures.iter().map(|signature| {
                        self.instantiate_signature_at_depth(*signature, mapper, depth + 1)
                    }),
                );
                if object.is_constructor_type {
                    instantiated.with_constructor_type(self.arena())
                } else {
                    instantiated
                }
            }
            TypeData::ModuleNamespace(namespace) => Ty::module_namespace(
                self.arena(),
                namespace.name,
                namespace.properties.iter().map(|property| TyProperty {
                    name: property.name,
                    computed: property.computed,
                    optional: property.optional,
                    method: property.method,
                    readonly: property.readonly,
                    ty: self.instantiate_type_at_depth(property.ty, mapper, depth + 1),
                }),
            ),
            TypeData::Function(function) => {
                let type_parameter_names = function
                    .type_parameters
                    .iter()
                    .map(|type_parameter| type_parameter.name)
                    .collect::<Vec<_>>();
                let mapper = mapper.without_type_parameter_names(
                    self.arena(),
                    type_parameter_names.iter().copied(),
                );

                let mut was_semantically_instantiated = false;
                let type_parameters = function
                    .type_parameters
                    .iter()
                    .map(|type_parameter| {
                        let constraint_type = type_parameter
                            .constraint_type
                            .map(|ty| self.instantiate_type_at_depth(ty, &mapper, depth + 1));
                        let default_type = type_parameter
                            .default_type
                            .map(|ty| self.instantiate_type_at_depth(ty, &mapper, depth + 1));
                        was_semantically_instantiated |= type_parameter
                            .constraint_type
                            .zip(constraint_type)
                            .is_some_and(|(original, instantiated)| {
                                !self.arena().is_type_identical_to(original, instantiated)
                            })
                            || type_parameter.default_type.zip(default_type).is_some_and(
                                |(original, instantiated)| {
                                    !self.arena().is_type_identical_to(original, instantiated)
                                },
                            );
                        Ty::type_parameter_with_display_default(
                            type_parameter.name,
                            constraint_type,
                            default_type,
                            type_parameter.display_default,
                        )
                    })
                    .collect::<Vec<_>>();
                let parameters = function
                    .parameters
                    .iter()
                    .map(|parameter| {
                        let ty = self.instantiate_type_at_depth(parameter.ty, &mapper, depth + 1);
                        was_semantically_instantiated |=
                            !self.arena().is_type_identical_to(parameter.ty, ty);
                        if parameter.rest {
                            Ty::rest_parameter(parameter.name, ty)
                        } else if parameter.optional {
                            Ty::optional_parameter(parameter.name, ty)
                        } else {
                            Ty::parameter(parameter.name, ty)
                        }
                    })
                    .collect::<Vec<_>>();
                let return_type =
                    self.instantiate_type_at_depth(function.return_type, &mapper, depth + 1);
                was_semantically_instantiated |= !self
                    .arena()
                    .is_type_identical_to(function.return_type, return_type);
                let type_predicate = function.type_predicate.map(|predicate| {
                    let target_type = predicate
                        .target_type
                        .map(|ty| self.instantiate_type_at_depth(ty, &mapper, depth + 1));
                    was_semantically_instantiated |= predicate
                        .target_type
                        .zip(target_type)
                        .is_some_and(|(original, instantiated)| {
                            !self.arena().is_type_identical_to(original, instantiated)
                        });
                    TyTypePredicate {
                        kind: predicate.kind,
                        parameter_name: predicate.parameter_name,
                        parameter_index: predicate.parameter_index,
                        target_type,
                    }
                });

                Ty::function_with_type_predicate_and_display(
                    self.arena(),
                    type_parameters,
                    parameters,
                    return_type,
                    type_predicate,
                    function.display_type_parameters_as_arguments || was_semantically_instantiated,
                )
            }
            TypeData::TypeReference(reference) => {
                let mapped = mapper.map(self.arena(), ty);
                if mapped != ty {
                    mapped
                } else {
                    let type_arguments = reference
                        .type_arguments
                        .iter()
                        .map(|ty| self.instantiate_type_at_depth(*ty, mapper, depth + 1))
                        .collect::<Vec<_>>();
                    if type_arguments == reference.type_arguments.as_slice() {
                        return ty;
                    }
                    let has_concrete_type_arguments = type_arguments
                        .iter()
                        .all(|ty| !self.could_contain_type_variables(*ty));
                    let instantiated = self
                        .rebuild_type_reference_with_display_type_argument_count(
                            ty,
                            type_arguments,
                            reference.display_type_argument_count,
                        );
                    // Conditional aliases are deferred until their arguments become concrete.
                    // Reduce them at mapper application so this works in any enclosing type.
                    if let Some(metadata) = self.type_alias_metadata(instantiated)
                        && has_concrete_type_arguments
                        && self.is_conditional_type_alias_declaration(
                            metadata.declaration.program_id,
                            metadata.declaration.node_id,
                        )
                    {
                        self.expand_type_at_use(
                            metadata.reference_program_id,
                            instantiated,
                            depth + 1,
                        )
                    } else {
                        instantiated
                    }
                }
            }
            TypeData::TypeQuery(query) => Ty::type_query(
                self.arena(),
                query.name,
                self.instantiate_type_at_depth(query.resolved, mapper, depth + 1),
                query
                    .type_arguments
                    .iter()
                    .map(|ty| self.instantiate_type_at_depth(*ty, mapper, depth + 1)),
            ),
            TypeData::Array(array) => {
                let element_type =
                    self.instantiate_type_at_depth(array.element_type, mapper, depth + 1);
                if array.display_as_generic {
                    Ty::generic_array(self.arena(), element_type, array.readonly)
                } else if array.readonly {
                    Ty::readonly_array(self.arena(), element_type)
                } else {
                    Ty::array(self.arena(), element_type)
                }
            }
            TypeData::Tuple(tuple) => {
                let elements = tuple
                    .elements
                    .iter()
                    .map(|element| match element {
                        TupleElement::Regular(ty) => TupleElement::Regular(
                            self.instantiate_type_at_depth(*ty, mapper, depth + 1),
                        ),
                        TupleElement::Rest(ty) => TupleElement::Rest(
                            self.instantiate_type_at_depth(*ty, mapper, depth + 1),
                        ),
                        TupleElement::Optional(ty) => TupleElement::Optional(
                            self.instantiate_type_at_depth(*ty, mapper, depth + 1),
                        ),
                    })
                    .collect::<Vec<_>>();
                Ty::tuple_with_labels(
                    self.arena(),
                    elements,
                    tuple.labels.iter().copied().collect(),
                    tuple.readonly,
                )
            }
            TypeData::Union(union) => Ty::r#union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.instantiate_type_at_depth(*ty, mapper, depth + 1)),
            ),
            TypeData::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection
                    .types
                    .iter()
                    .map(|ty| self.instantiate_type_at_depth(*ty, mapper, depth + 1)),
            ),
            TypeData::Keyof(keyof) => Ty::keyof(
                self.arena(),
                self.instantiate_type_at_depth(keyof.target, mapper, depth + 1),
            ),
            TypeData::IndexedAccess(indexed_access) => {
                let object_type =
                    self.instantiate_type_at_depth(indexed_access.object_type, mapper, depth + 1);
                let index_type =
                    self.instantiate_type_at_depth(indexed_access.index_type, mapper, depth + 1);
                if let (TypeData::Tuple(tuple), TypeData::StringLiteral(property)) = (
                    self.arena().type_data(object_type),
                    self.arena().type_data(index_type),
                ) && property.value == "length"
                {
                    self.get_property_type_of_tuple(object_type, tuple, property.value)
                        .unwrap_or_else(|| {
                            Ty::indexed_access(self.arena(), object_type, index_type)
                        })
                } else {
                    Ty::indexed_access(self.arena(), object_type, index_type)
                }
            }
            TypeData::Conditional(conditional) => {
                let infer_type_parameters =
                    self.infer_type_parameter_names(conditional.extends_type);
                let infer_mapper = mapper.without_type_parameter_names(
                    self.arena(),
                    infer_type_parameters.iter().copied(),
                );

                if conditional.is_distributive
                    && let TypeData::Union(union) = self
                        .arena()
                        .type_data(mapper.map(self.arena(), conditional.check_type))
                {
                    return Ty::r#union(
                        self.arena(),
                        union.types.iter().map(|ty| {
                            let member_mapper = mapper.with_prepend_mapping(
                                self.arena(),
                                conditional.check_type,
                                *ty,
                            );
                            let infer_member_mapper = member_mapper.without_type_parameter_names(
                                self.arena(),
                                infer_type_parameters.iter().copied(),
                            );
                            self.conditional_type(
                                *ty,
                                self.instantiate_type_at_depth(
                                    conditional.extends_type,
                                    &infer_member_mapper,
                                    depth + 1,
                                ),
                                self.instantiate_type_at_depth(
                                    conditional.true_type,
                                    &infer_member_mapper,
                                    depth + 1,
                                ),
                                self.instantiate_type_at_depth(
                                    conditional.false_type,
                                    &member_mapper,
                                    depth + 1,
                                ),
                                false,
                            )
                        }),
                    );
                }

                let check_type =
                    self.instantiate_type_at_depth(conditional.check_type, mapper, depth + 1);
                let extends_type = self.instantiate_type_at_depth(
                    conditional.extends_type,
                    &infer_mapper,
                    depth + 1,
                );
                if infer_type_parameters.is_empty()
                    && !self.could_contain_type_variables(check_type)
                    && !self.could_contain_type_variables(extends_type)
                {
                    let selected = if self.is_assignable_to(check_type, extends_type) {
                        conditional.true_type
                    } else {
                        conditional.false_type
                    };
                    return self.instantiate_type_at_depth(selected, mapper, depth + 1);
                }

                self.conditional_type(
                    check_type,
                    extends_type,
                    self.instantiate_type_at_depth(conditional.true_type, &infer_mapper, depth + 1),
                    self.instantiate_type_at_depth(conditional.false_type, mapper, depth + 1),
                    conditional.is_distributive,
                )
            }
            TypeData::Infer(infer) => {
                let mapper = mapper.without_type_parameter_names(
                    self.arena(),
                    std::iter::once(infer.type_parameter.name),
                );
                Ty::infer(
                    self.arena(),
                    Ty::type_parameter_with_display_default(
                        infer.type_parameter.name,
                        infer
                            .type_parameter
                            .constraint_type
                            .map(|ty| self.instantiate_type_at_depth(ty, &mapper, depth + 1)),
                        infer
                            .type_parameter
                            .default_type
                            .map(|ty| self.instantiate_type_at_depth(ty, &mapper, depth + 1)),
                        infer.type_parameter.display_default,
                    ),
                )
            }
            TypeData::Mapped(mapped) => {
                let mapper =
                    mapper.without_type_parameter_names(self.arena(), std::iter::once(mapped.key));
                Ty::mapped(
                    self.arena(),
                    mapped.key,
                    self.instantiate_type_at_depth(mapped.constraint, &mapper, depth + 1),
                    mapped
                        .name_type
                        .map(|ty| self.instantiate_type_at_depth(ty, &mapper, depth + 1)),
                    self.instantiate_type_at_depth(mapped.template, &mapper, depth + 1),
                    mapped.optional,
                    mapped.readonly,
                )
            }
            TypeData::This => mapper.map(self.arena(), ty),
            _ => ty,
        }
    }

    pub(crate) fn could_contain_type_variables(&self, ty: Ty<'a>) -> bool {
        let mut contains = false;
        visit_type(
            self.arena(),
            ty,
            &mut |ty| match self.arena().type_data(ty) {
                TypeData::TypeReference(reference) if reference.type_arguments.is_empty() => {
                    contains = true
                }
                TypeData::Function(function) if !function.type_parameters.is_empty() => {
                    contains = true
                }
                TypeData::This => contains = true,
                TypeData::Infer(_) => contains = true,
                _ => {}
            },
        );
        contains
    }

    fn contains_unresolved_type_parameter(&self, ty: Ty<'a>) -> bool {
        let mut contains = false;
        visit_type(
            self.arena(),
            ty,
            &mut |candidate| match self.arena().type_data(candidate) {
                TypeData::TypeReference(reference)
                    if reference.is_bare() && reference.target.is_none() =>
                {
                    contains = true;
                }
                TypeData::Infer(_) | TypeData::This => contains = true,
                _ => {}
            },
        );
        contains
    }

    fn is_generic_indexed_access(&self, object_type: Ty<'a>, index_type: Ty<'a>) -> bool {
        self.contains_unresolved_type_parameter(object_type)
            || self.contains_unresolved_type_parameter(index_type)
    }

    fn concrete_index_type_constraint(
        &self,
        program_id: ProgramId,
        node_id: Option<NodeId>,
        index_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        let node_id = node_id?;
        let constraint = self.get_type_parameter_constraint(program_id, node_id, index_type)?;
        let constraint = self.expand_type_for_index_lookup(program_id, constraint, 0);
        (!self.contains_unresolved_type_parameter(constraint)).then_some(constraint)
    }

    pub(crate) fn is_active_unresolved_type_alias(&self, ty: Ty<'a>) -> bool {
        self.could_contain_type_variables(ty)
            && self.type_alias_metadata(ty).is_some_and(|metadata| {
                self.resolving_type_aliases
                    .borrow()
                    .iter()
                    .any(|resolution| {
                        resolution.program_id == metadata.declaration.program_id
                            && resolution.declaration == metadata.declaration.node_id
                    })
            })
    }

    pub(crate) fn mark_type_instantiation_overflow(&self) {
        let should_propagate =
            self.resolving_type_aliases
                .borrow()
                .first()
                .is_some_and(|resolution| {
                    resolution.type_arguments.iter().all(|type_id| {
                        self.arena()
                            .type_from_id(*type_id)
                            .is_some_and(|ty| !self.could_contain_type_variables(ty))
                    })
                });
        if should_propagate {
            self.type_instantiation_overflowed.set(true);
        }
    }

    /// Resolve an expression type with a semantic context node when ancestor context is needed.
    /// This keeps `this` and member expressions tied to the class or call site they appear in.
    pub(crate) fn get_type_of_expression_with_node(
        &self,
        program_id: ProgramId,
        expression: &'a Expression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        self.check_expression_with_context(
            program_id,
            AstKind::from_expression(expression),
            node_id,
            ExpressionCheckContext::new(flags),
        )
    }

    fn check_expression_with_context(
        &self,
        program_id: ProgramId,
        expression: AstKind<'a>,
        node_id: Option<NodeId>,
        context: ExpressionCheckContext<'a>,
    ) -> Ty<'a> {
        let flags = context.flags;
        match expression {
            AstKind::IdentifierReference(identifier) => {
                let symbol = self
                    .symbol_for_identifier_reference(program_id, identifier)
                    .or_else(|| {
                        self.get_value_symbol_for_name(program_id, identifier.name.as_str())
                    });
                if let Some(symbol) = symbol {
                    let base_type = self.get_type_of_symbol(symbol);
                    if flags.context_free() {
                        return base_type;
                    }
                    return flow::get_flow_type_of_reference(
                        self,
                        self.identifier_node_ref(program_id, identifier),
                        symbol,
                        base_type,
                    );
                }
                if identifier.name == UNDEFINED_IDENT {
                    return Ty::undefined();
                }
                if identifier.name == GLOBAL_THIS_IDENT {
                    return Ty::global_this();
                }
                Ty::error(self.arena(), TypeErrorKind::UnresolvedSymbol)
            }
            AstKind::ObjectExpression(object) => {
                self.get_type_of_object_expression(program_id, object, node_id, context)
            }
            AstKind::BinaryExpression(binary_expression) => {
                self.get_type_of_binary_expression(program_id, binary_expression, node_id, flags)
            }
            AstKind::AssignmentExpression(assignment_expression) => self
                .get_type_of_assignment_expression(
                    program_id,
                    assignment_expression,
                    node_id,
                    flags,
                ),
            AstKind::ConditionalExpression(conditional) => {
                self.get_type_of_conditional_expression(program_id, conditional, node_id)
            }
            AstKind::UnaryExpression(unary_expression) => match unary_expression.operator {
                UnaryOperator::UnaryNegation | UnaryOperator::UnaryPlus => {
                    match &unary_expression.argument {
                        Expression::NumericLiteral(literal) if flags.preserve_literals() => {
                            Ty::number_literal_from_ast(
                                self.arena(),
                                literal,
                                unary_expression.operator == UnaryOperator::UnaryNegation,
                            )
                        }
                        _ => Ty::number(),
                    }
                }
                UnaryOperator::BitwiseNot => Ty::number(),
                UnaryOperator::LogicalNot => {
                    let argument_type = self.get_type_of_expression_with_node(
                        program_id,
                        &unary_expression.argument,
                        node_id,
                        flags | GetTypeFlags::PRESERVE_LITERALS,
                    );
                    type_facts::get_logical_not_type(self.arena(), argument_type)
                }
                UnaryOperator::Typeof => Ty::typeof_string_values(self.arena()),
                UnaryOperator::Void => Ty::undefined(),
                UnaryOperator::Delete => Ty::boolean(),
            },
            AstKind::TSNonNullExpression(non_null_expr) => {
                let ty = self.get_type_of_expression_with_node(
                    program_id,
                    &non_null_expr.expression,
                    node_id,
                    flags,
                );
                self.get_non_null_assertion_type(program_id, ty)
            }
            AstKind::NewExpression(new_expression) => {
                self.get_type_of_new_expression(program_id, new_expression, flags)
            }
            AstKind::CallExpression(call_expression) => {
                self.get_type_of_call_expression(program_id, call_expression, node_id)
            }
            AstKind::ArrayExpression(array_expression) => {
                self.get_type_of_array_expression(program_id, array_expression, node_id, context)
            }
            AstKind::ComputedMemberExpression(member) => {
                self.get_type_of_computed_member_expression(program_id, member, node_id, flags)
            }
            AstKind::StaticMemberExpression(member) => {
                self.get_type_of_static_member_expression(program_id, member, node_id, flags)
            }
            AstKind::ChainExpression(chain_expr) => {
                // Chain expressions have the same type as the property they are accessing, however they are
                // unioned with undefined, since the source object may be undefined.
                match &chain_expr.expression {
                    // `obj?.prop`
                    ChainElement::StaticMemberExpression(member_expr) => {
                        // Get type of `foo.bar` and then union it with undefined
                        let member_expr_type = self.get_type_of_static_member_expression(
                            program_id,
                            member_expr,
                            node_id,
                            flags,
                        );
                        member_expr_type.or_undefined(self.arena())
                    }
                    // `obj?.[prop]`
                    ChainElement::ComputedMemberExpression(computed_member_expression) => {
                        // Get type of `foo[bar]` and then union it with undefined
                        let computed_member_type = self.get_type_of_computed_member_expression(
                            program_id,
                            computed_member_expression,
                            node_id,
                            flags,
                        );
                        computed_member_type.or_undefined(self.arena())
                    }
                    ChainElement::CallExpression(call_expr) => self
                        .get_type_of_call_expression(program_id, call_expr, node_id)
                        .or_undefined(self.arena()),
                    ChainElement::PrivateFieldExpression(member) => self
                        .get_type_of_private_field_expression(program_id, member, node_id, flags)
                        .or_undefined(self.arena()),
                    ChainElement::TSNonNullExpression(non_null_expr) => {
                        let ty = self.get_type_of_expression_with_node(
                            program_id,
                            &non_null_expr.expression,
                            node_id,
                            flags,
                        );
                        self.get_non_null_assertion_type(program_id, ty)
                            .or_undefined(self.arena())
                    }
                }
            }

            AstKind::ParenthesizedExpression(parenthesized) => self.check_expression_with_context(
                program_id,
                AstKind::from_expression(&parenthesized.expression),
                node_id,
                context,
            ),
            AstKind::TSTypeAssertion(assertion) => {
                self.get_type_from_type_assertion(program_id, &assertion.type_annotation)
            }
            AstKind::TSAsExpression(assertion)
                if is_const_type_reference(&assertion.type_annotation) =>
            {
                let const_context = context
                    .with_flags(
                        flags | GetTypeFlags::CONTEXT_FREE | GetTypeFlags::PRESERVE_LITERALS,
                    )
                    .with_check_mode(CheckMode::CONST_CONTEXT | CheckMode::FORCE_TUPLE);
                self.check_expression_with_context(
                    program_id,
                    AstKind::from_expression(&assertion.expression),
                    node_id,
                    const_context,
                )
            }
            AstKind::TSAsExpression(assertion) => {
                self.get_type_from_type_assertion(program_id, &assertion.type_annotation)
            }
            AstKind::ThisExpression(_) => node_id
                .and_then(|node_id| self.get_enclosing_class_instance_type(program_id, node_id))
                .or_else(|| {
                    node_id.and_then(|node_id| {
                        self.get_contextual_this_type_of_object_literal_method(program_id, node_id)
                    })
                })
                .unwrap_or_else(Ty::any),
            AstKind::Function(function) if function.is_expression() => self
                .get_type_of_function_signature_with_node(
                    program_id,
                    FunctionKind::Function(function),
                    node_id,
                ),
            AstKind::ArrowFunctionExpression(arrow_function) => self
                .get_type_of_function_signature_with_node(
                    program_id,
                    FunctionKind::ArrowFunction(arrow_function),
                    node_id,
                ),
            AstKind::LogicalExpression(logical) => {
                self.get_type_of_logical_expression(program_id, logical, node_id, flags)
            }
            AstKind::AwaitExpression(await_expr) => {
                self.get_type_of_await_expression(program_id, await_expr, node_id)
            }
            AstKind::TSSatisfiesExpression(satisfies_expr) => {
                // `satisfies` mostly does not change the type, it just adds an additional assertion
                // on the apparent type for the type checker to verify against without changing the declared type.
                // However, it can change the type if the `satisfies` type is more specific than the apparent type.
                let target_type =
                    self.get_type_from_ts_type(program_id, &satisfies_expr.type_annotation);
                let target_type = self.expand_type_at_use(program_id, target_type, 0);
                let satisfies_context = context
                    .with_flags(
                        flags | GetTypeFlags::CONTEXT_FREE | GetTypeFlags::PRESERVE_LITERALS,
                    )
                    .with_contextual_type(target_type, CheckMode::CONTEXTUAL);
                self.check_expression_with_context(
                    program_id,
                    AstKind::from_expression(&satisfies_expr.expression),
                    node_id,
                    satisfies_context,
                )
            }
            AstKind::PrivateFieldExpression(member) => {
                self.get_type_of_private_field_expression(program_id, member, node_id, flags)
            }
            AstKind::NullLiteral(_) => Ty::null(),
            AstKind::NumericLiteral(literal) => {
                if flags.preserve_literals() {
                    Ty::number_literal_from_ast(self.arena(), literal, false)
                } else {
                    Ty::number()
                }
            }
            AstKind::StringLiteral(literal) => {
                if flags.preserve_literals() {
                    Ty::string_literal(self.arena(), self.get_string_literal_value(literal))
                } else {
                    Ty::string()
                }
            }
            AstKind::BooleanLiteral(literal) => {
                if flags.preserve_literals() {
                    Ty::boolean_literal(literal.value)
                } else {
                    Ty::boolean()
                }
            }
            AstKind::BigIntLiteral(literal) => {
                if flags.preserve_literals() {
                    Ty::bigint_literal(self.arena(), self.get_bigint_literal_value(literal))
                } else {
                    Ty::bigint()
                }
            }
            AstKind::TemplateLiteral(literal) => {
                if flags.preserve_literals() {
                    if let Some(value) =
                        self.get_template_literal_static_value(program_id, literal, node_id)
                    {
                        Ty::string_literal(self.arena(), value)
                    } else if literal.expressions.is_empty() {
                        Ty::template_literal(
                            self.arena(),
                            literal.quasis.iter().map(|q| TemplateLiteralElement {
                                value: q.value.raw.as_str(),
                            }),
                            literal.expressions.iter().map(|e| {
                                self.get_type_of_expression_with_node(
                                    program_id,
                                    e,
                                    node_id,
                                    GetTypeFlags::NONE,
                                )
                            }),
                        )
                    } else {
                        Ty::string()
                    }
                } else {
                    Ty::string()
                }
            }
            AstKind::RegExpLiteral(_) => self.get_global_regexp_type(program_id),
            AstKind::Super(_) => node_id
                .and_then(|node_id| {
                    self.get_enclosing_base_class_instance_type(program_id, node_id)
                })
                .unwrap_or_else(|| Ty::error(self.arena(), TypeErrorKind::UnresolvedType)),
            AstKind::Class(class) if class.is_expression() => {
                self.get_type_of_class_expression(program_id, class)
            }
            AstKind::ImportMeta(_) => self.type_reference_with_display_type_argument_count(
                program_id,
                "ImportMeta",
                std::iter::empty(),
                0,
            ),
            AstKind::NewTarget(_) => node_id
                .and_then(|node_id| self.get_type_of_new_target(program_id, node_id))
                .unwrap_or_else(|| Ty::error(self.arena(), TypeErrorKind::UnresolvedType)),
            AstKind::ImportExpression(import_expression) => {
                self.get_type_of_import_expression(program_id, import_expression)
            }
            AstKind::SequenceExpression(sequence) => sequence
                .expressions
                .iter()
                .map(|expression| {
                    self.get_type_of_expression_with_node(program_id, expression, node_id, flags)
                })
                .last()
                .unwrap_or_else(|| Ty::error(self.arena(), TypeErrorKind::UnresolvedType)),
            AstKind::TaggedTemplateExpression(tagged_template) => {
                self.get_type_of_tagged_template_expression(program_id, tagged_template, node_id)
            }
            AstKind::UpdateExpression(update) => {
                let target_type = self.get_type_of_simple_assignment_target(
                    program_id,
                    &update.argument,
                    node_id,
                    flags | GetTypeFlags::CONTEXT_FREE,
                );
                let target_type = self.expand_type_at_use(program_id, target_type, 0);
                match self.arena().type_data(target_type) {
                    TypeData::Bigint | TypeData::BigIntLiteral(_) => Ty::bigint(),
                    _ => Ty::number(),
                }
            }
            AstKind::YieldExpression(yield_expression) => {
                self.get_type_of_yield_expression(program_id, yield_expression)
            }
            AstKind::PrivateInExpression(_) => Ty::boolean(),
            // TODO(correctness): Handle all of these cases.
            AstKind::JSXElement(_) => Ty::error(self.arena(), TypeErrorKind::UnsupportedType),
            AstKind::JSXFragment(_) => Ty::error(self.arena(), TypeErrorKind::UnsupportedType),
            AstKind::TSInstantiationExpression(_) => {
                Ty::error(self.arena(), TypeErrorKind::UnsupportedType)
            }
            AstKind::V8IntrinsicExpression(_) => {
                Ty::error(self.arena(), TypeErrorKind::UnsupportedType)
            }
            _ => unreachable!("expected expression AST kind"),
        }
    }

    fn get_type_of_import_expression(
        &self,
        program_id: ProgramId,
        import_expression: &'a ImportExpression<'a>,
    ) -> Ty<'a> {
        let imported_type = match &import_expression.source {
            Expression::StringLiteral(source) => self
                .store
                .resolved_module(program_id, source.value.as_str())
                .map_or_else(
                    || Ty::error(self.arena(), TypeErrorKind::UnresolvedImport),
                    |imported_program_id| {
                        let module_type = self
                            .get_module_namespace_type(imported_program_id, source.value.as_str());
                        let name = self
                            .arena()
                            .str(&format!("import(\"{}\")", source.value.as_str()));
                        Ty::type_query(self.arena(), name, module_type, std::iter::empty())
                    },
                ),
            _ => Ty::error(self.arena(), TypeErrorKind::UnsupportedType),
        };

        let promise_type = self.get_global_promise_type(program_id);
        let TypeData::TypeReference(reference) = self.arena().type_data(promise_type) else {
            return Ty::error(self.arena(), TypeErrorKind::UnresolvedType);
        };
        Ty::type_reference(self.arena(), reference.name, [imported_type])
    }

    fn get_type_of_new_target(&self, program_id: ProgramId, node_id: NodeId) -> Option<Ty<'a>> {
        for ancestor in self.nodes(program_id).ancestors(node_id) {
            match ancestor.kind() {
                AstKind::ArrowFunctionExpression(_) => {}
                AstKind::Function(function) => {
                    if matches!(
                        self.nodes(program_id).parent_kind(function.node_id()),
                        AstKind::MethodDefinition(method)
                            if method.kind == MethodDefinitionKind::Constructor
                    ) {
                        let class_name = self
                            .nodes(program_id)
                            .ancestors(function.node_id())
                            .find_map(|ancestor| match ancestor.kind() {
                                AstKind::Class(class) => {
                                    class.id.as_ref().map(|identifier| identifier.name.as_str())
                                }
                                _ => None,
                            });
                        return class_name.map_or_else(
                            || Some(Ty::error(self.arena(), TypeErrorKind::UnresolvedSymbol)),
                            |class_name| {
                                Some(Ty::type_query(
                                    self.arena(),
                                    class_name,
                                    Ty::error(self.arena(), TypeErrorKind::UnresolvedSymbol),
                                    std::iter::empty(),
                                ))
                            },
                        );
                    }

                    if matches!(
                        self.nodes(program_id).parent_kind(function.node_id()),
                        AstKind::MethodDefinition(_)
                    ) {
                        return Some(Ty::error(self.arena(), TypeErrorKind::UnresolvedType));
                    }

                    if let Some(symbol_id) = function
                        .id
                        .as_ref()
                        .and_then(|identifier| identifier.symbol_id.get())
                    {
                        return Some(
                            self.get_type_of_symbol(SymbolRef::new(program_id, symbol_id)),
                        );
                    }

                    if let Some(symbol) = self
                        .nodes(program_id)
                        .ancestors(function.node_id())
                        .find_map(|ancestor| match ancestor.kind() {
                            AstKind::VariableDeclarator(declarator)
                                if declarator
                                    .init
                                    .as_ref()
                                    .is_some_and(|init| init.span() == function.span) =>
                            {
                                self.simple_binding_symbol(program_id, &declarator.id)
                            }
                            _ => None,
                        })
                    {
                        return Some(self.get_type_of_symbol(symbol));
                    }

                    let type_parameters = self.type_parameters_from_declaration(
                        program_id,
                        function.type_parameters.as_deref(),
                    );
                    let parameters =
                        self.function_signature_parameters(program_id, &function.params);
                    return Some(Ty::function_with_type_predicate(
                        self.arena(),
                        type_parameters,
                        parameters,
                        Ty::any(),
                        None,
                    ));
                }
                _ => {}
            }
        }
        None
    }

    fn identifier_node_ref(
        &self,
        program_id: ProgramId,
        identifier: &IdentifierReference<'a>,
    ) -> NodeRef {
        NodeRef::new(program_id, identifier.node_id())
    }

    fn is_in_exported_declaration(&self, program_id: ProgramId, node_id: NodeId) -> bool {
        self.nodes(program_id).ancestor_kinds(node_id).any(|kind| {
            matches!(
                kind,
                AstKind::ExportNamedDeclaration(_)
                    | AstKind::ExportDefaultDeclaration(_)
                    | AstKind::ExportAllDeclaration(_)
            )
        })
    }

    fn get_type_symbol_for_export_specifier_local(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        identifier: &IdentifierReference<'a>,
    ) -> Option<SymbolRef> {
        let AstKind::ExportSpecifier(specifier) = self.nodes(program_id).parent_kind(node_id)
        else {
            return None;
        };
        let ModuleExportName::IdentifierReference(local) = &specifier.local else {
            return None;
        };
        if local.span != identifier.span {
            return None;
        }
        self.get_type_symbol_in_program(program_id, identifier.name.as_str())
    }

    fn get_type_of_export_specifier_local(
        &self,
        program_id: ProgramId,
        specifier: &ExportSpecifier<'a>,
    ) -> Ty<'a> {
        let Some(local_name) = specifier.local.identifier_name() else {
            return Ty::none();
        };
        let local_name = local_name.as_str();

        self.get_type_symbol_in_program(program_id, local_name)
            .and_then(|symbol| {
                let ty = self.get_type_of_symbol(symbol);
                if ty.is_none() { None } else { Some(ty) }
            })
            .or_else(|| self.get_type_of_local_type_declaration_by_name(program_id, local_name))
            .unwrap_or_else(Ty::none)
    }

    fn get_type_of_local_type_declaration_by_name(
        &self,
        program_id: ProgramId,
        type_name: &str,
    ) -> Option<Ty<'a>> {
        self.semantic(program_id)
            .nodes()
            .iter()
            .find_map(|node| match node.kind() {
                AstKind::TSInterfaceDeclaration(interface)
                    if interface.id.name.as_str() == type_name =>
                {
                    Some(Ty::error(self.arena(), TypeErrorKind::UnsupportedType))
                }
                AstKind::TSTypeAliasDeclaration(alias) if alias.id.name.as_str() == type_name => {
                    let ty = self.get_type_of_type_alias_declaration(program_id, alias);
                    Some(if ty.is_none() {
                        Ty::error(self.arena(), TypeErrorKind::UnresolvedType)
                    } else {
                        ty
                    })
                }
                _ => None,
            })
    }

    /// Removes `null` and `undefined` from the type, like when using `!` or `NonNullable<T>`.
    pub(crate) fn remove_null_or_undefined(&self, ty: Ty<'a>) -> Ty<'a> {
        match ty {
            Ty::Null | Ty::Undefined => Ty::never(),
            _ => ty.map_union(self.arena(), |ty| match ty {
                Ty::Null | Ty::Undefined => None,
                _ => Some(ty),
            }),
        }
    }

    fn remove_undefined(&self, ty: Ty<'a>) -> Ty<'a> {
        if ty == Ty::Undefined {
            Ty::never()
        } else {
            ty.map_union(self.arena(), |ty| (ty != Ty::Undefined).then_some(ty))
        }
    }

    fn get_non_null_assertion_type(&self, program_id: ProgramId, ty: Ty<'a>) -> Ty<'a> {
        let non_nullish = self.remove_null_or_undefined(ty);
        if self.could_contain_type_variables(non_nullish) {
            return self.get_global_non_nullable_type(program_id, non_nullish);
        }
        non_nullish
    }

    pub(crate) fn get_string_literal_value(&self, literal: &StringLiteral<'a>) -> &'a str {
        literal.value.as_str()
    }

    // TODO(cleanup): just allow bigint literals to store all the info instead of just str
    pub(crate) fn get_bigint_literal_value(&self, literal: &BigIntLiteral<'a>) -> &'a str {
        literal
            .raw
            .as_ref()
            .map_or_else(
                || self.arena().str(&format!("{:?}", literal.value)),
                |raw| raw.as_str(),
            )
            .trim_end_matches('n')
    }

    fn get_type_of_binary_expression(
        &self,
        program_id: ProgramId,
        binary_expression: &'a BinaryExpression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        let left = self.get_type_of_expression_with_node(
            program_id,
            &binary_expression.left,
            node_id,
            flags,
        );
        let right = self.get_type_of_expression_with_node(
            program_id,
            &binary_expression.right,
            node_id,
            flags,
        );

        match binary_expression.operator {
            BinaryOperator::Equality => Ty::boolean(),
            BinaryOperator::Inequality => Ty::boolean(),
            BinaryOperator::StrictEquality => Ty::boolean(),
            BinaryOperator::StrictInequality => Ty::boolean(),
            BinaryOperator::LessThan => Ty::boolean(),
            BinaryOperator::LessEqualThan => Ty::boolean(),
            BinaryOperator::GreaterThan => Ty::boolean(),
            BinaryOperator::GreaterEqualThan => Ty::boolean(),
            BinaryOperator::Addition
                if self.is_string_like_for_addition(left)
                    || self.is_string_like_for_addition(right) =>
            {
                Ty::string()
            }
            BinaryOperator::Addition => Ty::number(),
            BinaryOperator::Subtraction => Ty::number(),
            BinaryOperator::Multiplication => Ty::number(),
            BinaryOperator::Division => Ty::number(),
            BinaryOperator::Remainder => Ty::number(),
            BinaryOperator::Exponential => Ty::number(),
            BinaryOperator::ShiftLeft => Ty::number(),
            BinaryOperator::ShiftRight => Ty::number(),
            BinaryOperator::ShiftRightZeroFill => Ty::number(),
            BinaryOperator::BitwiseOR => Ty::number(),
            BinaryOperator::BitwiseXOR => Ty::number(),
            BinaryOperator::BitwiseAnd => Ty::number(),
            BinaryOperator::In => Ty::boolean(),
            BinaryOperator::Instanceof => Ty::boolean(),
        }
    }

    fn get_type_of_assignment_expression(
        &self,
        program_id: ProgramId,
        assignment_expression: &'a AssignmentExpression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        let left = self.get_type_of_assignment_target(
            program_id,
            &assignment_expression.left,
            node_id,
            flags | GetTypeFlags::CONTEXT_FREE,
        );
        let right = self.get_type_of_expression_with_node(
            program_id,
            &assignment_expression.right,
            node_id,
            flags | GetTypeFlags::PRESERVE_LITERALS,
        );
        match assignment_expression.operator {
            AssignmentOperator::Assign => right,
            AssignmentOperator::Addition => {
                if self.is_string_like_for_addition(left) || self.is_string_like_for_addition(right)
                {
                    Ty::string()
                } else if left.is_any_like(self.arena()) {
                    left
                } else {
                    Ty::number()
                }
            }
            AssignmentOperator::Subtraction
            | AssignmentOperator::Multiplication
            | AssignmentOperator::Division
            | AssignmentOperator::Remainder
            | AssignmentOperator::Exponential => Ty::number(),
            AssignmentOperator::ShiftLeft => Ty::number(),
            AssignmentOperator::ShiftRight => Ty::number(),
            AssignmentOperator::ShiftRightZeroFill => Ty::number(),
            AssignmentOperator::BitwiseOR => Ty::number(),
            AssignmentOperator::BitwiseXOR => Ty::number(),
            AssignmentOperator::BitwiseAnd => Ty::number(),
            AssignmentOperator::LogicalOr => {
                Ty::union(self.arena(), [self.get_truthy_type(left), right])
            }
            AssignmentOperator::LogicalAnd => {
                Ty::union(self.arena(), [self.get_falsy_type(left), right])
            }
            AssignmentOperator::LogicalNullish => {
                Ty::union(self.arena(), [self.remove_null_or_undefined(left), right])
            }
        }
    }

    fn get_type_of_logical_expression(
        &self,
        program_id: ProgramId,
        logical: &'a LogicalExpression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        let left = self.get_type_of_expression_with_node(program_id, &logical.left, node_id, flags);
        let right =
            self.get_type_of_expression_with_node(program_id, &logical.right, node_id, flags);
        match logical.operator {
            LogicalOperator::Or => Ty::union(self.arena(), [self.get_truthy_type(left), right]),
            LogicalOperator::And => Ty::union(self.arena(), [self.get_falsy_type(left), right]),
            LogicalOperator::Coalesce => {
                Ty::union(self.arena(), [self.remove_null_or_undefined(left), right])
            }
        }
    }

    fn get_type_of_assignment_target(
        &self,
        program_id: ProgramId,
        target: &'a AssignmentTarget<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        if let Some(target) = target.as_simple_assignment_target() {
            return self.get_type_of_simple_assignment_target(program_id, target, node_id, flags);
        }
        Ty::error(self.arena(), TypeErrorKind::UnsupportedType)
    }

    fn get_type_of_simple_assignment_target(
        &self,
        program_id: ProgramId,
        target: &'a SimpleAssignmentTarget<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        match target {
            SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) => {
                let symbol = self
                    .symbol_for_identifier_reference(program_id, identifier)
                    .or_else(|| {
                        self.get_value_symbol_for_name(program_id, identifier.name.as_str())
                    });
                if let Some(symbol) = symbol {
                    return self.get_type_of_symbol(symbol);
                }
                if identifier.name == UNDEFINED_IDENT {
                    return Ty::undefined();
                }
                Ty::error(self.arena(), TypeErrorKind::UnresolvedSymbol)
            }
            SimpleAssignmentTarget::ComputedMemberExpression(member) => {
                self.get_type_of_computed_member_expression(program_id, member, node_id, flags)
            }
            SimpleAssignmentTarget::StaticMemberExpression(member) => {
                self.get_type_of_static_member_expression(program_id, member, node_id, flags)
            }
            SimpleAssignmentTarget::TSAsExpression(assertion) => self
                .get_type_of_expression_with_node(
                    program_id,
                    &assertion.expression,
                    node_id,
                    flags,
                ),
            SimpleAssignmentTarget::TSSatisfiesExpression(satisfies) => self
                .get_type_of_expression_with_node(
                    program_id,
                    &satisfies.expression,
                    node_id,
                    flags,
                ),
            SimpleAssignmentTarget::TSNonNullExpression(non_null) => {
                let ty = self.get_type_of_expression_with_node(
                    program_id,
                    &non_null.expression,
                    node_id,
                    flags,
                );
                self.get_non_null_assertion_type(program_id, ty)
            }
            SimpleAssignmentTarget::TSTypeAssertion(assertion) => self
                .get_type_of_expression_with_node(
                    program_id,
                    &assertion.expression,
                    node_id,
                    flags,
                ),
            SimpleAssignmentTarget::PrivateFieldExpression(_) => {
                Ty::error(self.arena(), TypeErrorKind::UnsupportedType)
            }
        }
    }

    fn get_truthy_type(&self, ty: Ty<'a>) -> Ty<'a> {
        match self.arena().type_data(ty) {
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union.types.iter().map(|ty| self.get_truthy_type(*ty)),
            ),
            TypeData::Boolean => Ty::boolean_true(),
            TypeData::BooleanLiteral(false) | TypeData::StringLiteral(_)
                if type_facts::get_type_facts(self.arena(), ty, type_facts::TypeFacts::TRUTHY)
                    .is_empty() =>
            {
                Ty::never()
            }
            TypeData::NumberLiteral(literal) if literal.value == 0.0 => Ty::never(),
            TypeData::BigIntLiteral(_)
                if type_facts::get_type_facts(self.arena(), ty, type_facts::TypeFacts::TRUTHY)
                    .is_empty() =>
            {
                Ty::never()
            }
            TypeData::Null | TypeData::Undefined | TypeData::Void => Ty::never(),
            _ => ty,
        }
    }

    fn get_falsy_type(&self, ty: Ty<'a>) -> Ty<'a> {
        match self.arena().type_data(ty) {
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union.types.iter().map(|ty| self.get_falsy_type(*ty)),
            ),
            TypeData::String => Ty::string_literal(self.arena(), ""),
            TypeData::Number => Ty::number_literal(self.arena(), 0.0, "0", NumberBase::Decimal),
            TypeData::Bigint => Ty::bigint_literal(self.arena(), "0"),
            TypeData::Boolean => Ty::boolean_false(),
            TypeData::StringLiteral(_)
            | TypeData::NumberLiteral(_)
            | TypeData::BooleanLiteral(_)
            | TypeData::BigIntLiteral(_)
            | TypeData::Null
            | TypeData::Undefined
            | TypeData::Void
                if type_facts::get_type_facts(self.arena(), ty, type_facts::TypeFacts::FALSY)
                    .is_empty() =>
            {
                Ty::never()
            }
            _ if type_facts::get_type_facts(self.arena(), ty, type_facts::TypeFacts::FALSY)
                .is_empty() =>
            {
                Ty::never()
            }
            _ => ty,
        }
    }

    fn get_template_literal_static_value(
        &self,
        program_id: ProgramId,
        literal: &'a TemplateLiteral<'a>,
        node_id: Option<NodeId>,
    ) -> Option<&'a str> {
        let mut value = String::new();
        for (index, quasi) in literal.quasis.iter().enumerate() {
            value.push_str(quasi.value.cooked.as_ref()?.as_str());
            if let Some(expression) = literal.expressions.get(index) {
                let expression_type = self.get_type_of_expression_with_node(
                    program_id,
                    expression,
                    node_id,
                    GetTypeFlags::CONTEXT_FREE | GetTypeFlags::PRESERVE_LITERALS,
                );
                value
                    .push_str(self.template_expression_substitution_static_value(expression_type)?);
            }
        }
        Some(self.arena().str(&value))
    }

    fn template_expression_substitution_static_value(&self, ty: Ty<'a>) -> Option<&'a str> {
        match self.arena().type_data(ty) {
            TypeData::StringLiteral(_) | TypeData::NumberLiteral(_) => {
                self.template_substitution_static_value(ty)
            }
            _ => None,
        }
    }

    fn template_substitution_static_value(&self, ty: Ty<'a>) -> Option<&'a str> {
        match self.arena().type_data(ty) {
            TypeData::StringLiteral(literal) => Some(string_literal_type_to_property_name(
                self.arena(),
                literal.value,
            )),
            TypeData::NumberLiteral(literal) => Some(if literal.value == 0.0 {
                "0"
            } else {
                self.arena().str(&literal.value.to_string())
            }),
            TypeData::BooleanLiteral(value) => Some(if value { "true" } else { "false" }),
            TypeData::Null => Some("null"),
            TypeData::Undefined | TypeData::Void => Some("undefined"),
            TypeData::TemplateLiteral(template) if template.expressions.is_empty() => {
                Some(template.quasis[0].value)
            }
            _ => None,
        }
    }

    fn template_substitution_static_values(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
    ) -> Option<Vec<&'a str>> {
        let ty = self.expand_type_at_use(program_id, ty, 0);
        let ty = self
            .get_enum_literal_union_type(program_id, ty)
            .unwrap_or(ty);
        match self.arena().type_data(ty) {
            TypeData::Union(union) => union.types.iter().try_fold(Vec::new(), |mut values, ty| {
                values.extend(self.template_substitution_static_values(program_id, *ty)?);
                Some(values)
            }),
            _ => Some(vec![self.template_substitution_static_value(ty)?]),
        }
    }

    fn get_enum_literal_union_type(&self, program_id: ProgramId, ty: Ty<'a>) -> Option<Ty<'a>> {
        let TypeData::TypeReference(reference) = self.arena().type_data(ty) else {
            return None;
        };
        if let Some((symbol, declaration)) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)
        {
            return self.get_enum_literal_union_from_declaration(symbol.program_id, declaration);
        }

        let (enum_name, member_name) = reference.name.rsplit_once('.')?;
        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, enum_name)?;
        self.get_enum_member_literal_from_declaration(symbol.program_id, declaration, member_name)
    }

    fn get_enum_member_literal_from_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        member_name: &str,
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSEnumDeclaration(enum_declaration) => {
                let member = enum_declaration
                    .body
                    .members
                    .iter()
                    .find(|member| member.id.static_name() == member_name)?;
                Some(self.get_type_of_expression_with_node(
                    program_id,
                    member.initializer.as_ref()?,
                    None,
                    GetTypeFlags::PRESERVE_LITERALS,
                ))
            }
            AstKind::BindingIdentifier(_) => self.get_enum_member_literal_from_declaration(
                program_id,
                self.nodes(program_id).parent_id(declaration),
                member_name,
            ),
            _ => None,
        }
    }

    fn get_enum_member_symbol_for_name(
        &self,
        program_id: ProgramId,
        name: &str,
    ) -> Option<SymbolRef> {
        let (enum_name, member_name) = name.rsplit_once('.')?;
        let (enum_symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, enum_name)?;
        self.get_enum_member_symbol_from_declaration(
            enum_symbol.program_id,
            declaration,
            member_name,
        )
    }

    fn get_enum_member_symbol_from_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        member_name: &str,
    ) -> Option<SymbolRef> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSEnumDeclaration(declaration) => declaration
                .body
                .scope_id
                .get()
                .and_then(|scope_id| {
                    self.semantic(program_id)
                        .scoping()
                        .get_binding(scope_id, Ident::from(member_name))
                })
                .map(|symbol_id| SymbolRef::new(program_id, symbol_id)),
            AstKind::BindingIdentifier(_) => self.get_enum_member_symbol_from_declaration(
                program_id,
                self.nodes(program_id).parent_id(declaration),
                member_name,
            ),
            _ => None,
        }
    }

    fn get_enum_literal_union_from_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            // TODO(correctness): Evaluate implicit and computed enum member values.
            AstKind::TSEnumDeclaration(enum_declaration) => Some(Ty::union(
                self.arena(),
                enum_declaration
                    .body
                    .members
                    .iter()
                    .map(|member| {
                        self.get_type_of_expression_with_node(
                            program_id,
                            member.initializer.as_ref()?,
                            None,
                            GetTypeFlags::PRESERVE_LITERALS,
                        )
                        .into()
                    })
                    .collect::<Option<Vec<_>>>()?,
            )),
            AstKind::TSEnumMember(member) => Some(self.get_type_of_expression_with_node(
                program_id,
                member.initializer.as_ref()?,
                None,
                GetTypeFlags::PRESERVE_LITERALS,
            )),
            AstKind::BindingIdentifier(_) => self.get_enum_literal_union_from_declaration(
                program_id,
                self.nodes(program_id).parent_id(declaration),
            ),
            _ => None,
        }
    }

    fn get_type_of_enum_declaration(
        &self,
        program_id: ProgramId,
        declaration: &'a oxc_ast::ast::TSEnumDeclaration<'a>,
    ) -> Ty<'a> {
        let enum_name = declaration.id.name.as_str();
        let member_types = declaration
            .body
            .members
            .iter()
            .map(|member| self.get_type_of_enum_member_reference(program_id, declaration, member))
            .collect::<Vec<_>>();
        let object_type =
            Ty::object(
                self.arena(),
                declaration
                    .body
                    .members
                    .iter()
                    .zip(&member_types)
                    .map(|(member, ty)| {
                        let member_name = member.id.static_name();
                        TyProperty {
                            name: member_name.as_str(),
                            ty: *ty,
                            computed: false,
                            optional: false,
                            method: false,
                            readonly: true,
                        }
                    }),
            )
            .with_index_infos(
                self.arena(),
                [IndexInfo::new(
                    "x",
                    Ty::string(),
                    if declaration.body.members.iter().all(|member| {
                        matches!(member.initializer, Some(Expression::StringLiteral(_)))
                    }) {
                        Ty::type_reference(self.arena(), enum_name, [])
                    } else {
                        Ty::union(
                            self.arena(),
                            std::iter::once(Ty::string()).chain(
                                declaration
                                    .body
                                    .members
                                    .iter()
                                    .zip(member_types)
                                    .filter_map(|(member, ty)| {
                                        (!matches!(
                                            member.initializer,
                                            Some(Expression::StringLiteral(_))
                                        ))
                                        .then_some(ty)
                                    }),
                            ),
                        )
                    },
                    true,
                )],
            );
        Ty::type_query(self.arena(), enum_name, object_type, [])
    }

    fn get_type_of_enum_member_reference(
        &self,
        program_id: ProgramId,
        declaration: &'a oxc_ast::ast::TSEnumDeclaration<'a>,
        member: &'a oxc_ast::ast::TSEnumMember<'a>,
    ) -> Ty<'a> {
        let member_name = member.id.static_name();
        let name = self
            .arena()
            .str(&format!("{}.{}", declaration.id.name.as_str(), member_name));
        let target = declaration.body.scope_id.get().and_then(|scope_id| {
            self.semantic(program_id)
                .scoping()
                .get_binding(scope_id, Ident::from(member_name.as_str()))
                .map(|symbol_id| SymbolRef::new(program_id, symbol_id))
        });
        target.map_or_else(
            || Ty::type_reference(self.arena(), name, []),
            |target| Ty::type_reference_for_symbol(self.arena(), name, target, [], 0),
        )
    }

    fn get_type_of_enum_member(
        &self,
        program_id: ProgramId,
        member: &'a oxc_ast::ast::TSEnumMember<'a>,
    ) -> Ty<'a> {
        let declaration = self
            .nodes(program_id)
            .ancestor_kinds(member.node_id())
            .find_map(|kind| match kind {
                AstKind::TSEnumDeclaration(declaration) => Some(declaration),
                _ => None,
            });
        declaration.map_or_else(Ty::none, |declaration| {
            self.get_type_of_enum_member_reference(program_id, declaration, member)
        })
    }

    fn get_template_literal_type(
        &self,
        program_id: ProgramId,
        quasis: impl IntoIterator<Item = TemplateLiteralElement<'a>>,
        expressions: impl IntoIterator<Item = Ty<'a>>,
    ) -> Ty<'a> {
        let quasis = quasis.into_iter().collect::<Vec<_>>();
        let expressions = expressions.into_iter().collect::<Vec<_>>();

        if quasis.len() == expressions.len() + 1 {
            let mut values = vec![String::from(quasis[0].value)];
            let mut is_static = true;
            for (expression, quasi) in expressions.iter().zip(&quasis[1..]) {
                let Some(substitutions) =
                    self.template_substitution_static_values(program_id, *expression)
                else {
                    is_static = false;
                    break;
                };
                values = values
                    .iter()
                    .flat_map(|value| {
                        substitutions.iter().map(|substitution| {
                            let mut value = value.clone();
                            value.push_str(substitution);
                            value.push_str(quasi.value);
                            value
                        })
                    })
                    .collect();
            }
            if is_static {
                return Ty::union(
                    self.arena(),
                    values
                        .iter()
                        .map(|value| Ty::string_literal(self.arena(), self.arena().str(value))),
                );
            }
        }

        Ty::template_literal(self.arena(), quasis, expressions)
    }

    fn get_type_of_conditional_expression(
        &self,
        program_id: ProgramId,
        conditional: &'a ConditionalExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let consequent = self.get_type_of_expression_with_node(
            program_id,
            &conditional.consequent,
            node_id,
            GetTypeFlags::PRESERVE_LITERALS,
        );
        let alternate = self.get_type_of_expression_with_node(
            program_id,
            &conditional.alternate,
            node_id,
            GetTypeFlags::PRESERVE_LITERALS,
        );

        Ty::union(self.arena(), [consequent, alternate])
    }

    fn is_string_like_for_addition(&self, ty: Ty<'a>) -> bool {
        matches!(
            self.arena().type_data(ty),
            TypeData::String | TypeData::StringLiteral(_)
        )
    }

    /// Resolve a TypeScript type annotation, if any.
    fn get_type_from_ts_type_annotation(
        &self,
        program_id: ProgramId,
        type_annotation: Option<&'a TSTypeAnnotation<'a>>,
    ) -> Ty<'a> {
        type_annotation.map_or_else(Ty::any, |type_annotation| {
            let ty = self.get_type_from_ts_type(program_id, &type_annotation.type_annotation);
            if self.hide_implicit_type_argument_display.get() {
                ty
            } else {
                self.with_implicit_type_arguments_visible(ty)
            }
        })
    }

    pub(crate) fn with_implicit_type_arguments_visible(&self, ty: Ty<'a>) -> Ty<'a> {
        match self.arena().type_data(ty) {
            TypeData::TypeReference(reference) => {
                let display_type_argument_count = if reference.display_type_argument_count == 0 {
                    reference.type_arguments.len()
                } else {
                    reference.display_type_argument_count
                };
                self.rebuild_type_reference_with_display_type_argument_count(
                    ty,
                    reference
                        .type_arguments
                        .iter()
                        .map(|ty| self.with_implicit_type_arguments_visible(*ty)),
                    display_type_argument_count,
                )
            }
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.with_implicit_type_arguments_visible(*ty)),
            ),
            TypeData::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection
                    .types
                    .iter()
                    .map(|ty| self.with_implicit_type_arguments_visible(*ty)),
            ),
            TypeData::Array(array) => {
                let element_type = self.with_implicit_type_arguments_visible(array.element_type);
                if array.display_as_generic {
                    Ty::generic_array(self.arena(), element_type, array.readonly)
                } else if array.readonly {
                    Ty::readonly_array(self.arena(), element_type)
                } else {
                    Ty::array(self.arena(), element_type)
                }
            }
            TypeData::Tuple(tuple) => {
                let elements = tuple
                    .elements
                    .iter()
                    .map(|element| match element {
                        TupleElement::Regular(ty) => {
                            TupleElement::Regular(self.with_implicit_type_arguments_visible(*ty))
                        }
                        TupleElement::Rest(ty) => {
                            TupleElement::Rest(self.with_implicit_type_arguments_visible(*ty))
                        }
                        TupleElement::Optional(ty) => {
                            TupleElement::Optional(self.with_implicit_type_arguments_visible(*ty))
                        }
                    })
                    .collect::<Vec<_>>();
                Ty::tuple_with_labels(
                    self.arena(),
                    elements,
                    tuple.labels.iter().copied().collect(),
                    tuple.readonly,
                )
            }
            _ => ty,
        }
    }

    fn rebuild_type_reference_with_display_type_argument_count(
        &self,
        source: Ty<'a>,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
        display_type_argument_count: usize,
    ) -> Ty<'a> {
        let TypeData::TypeReference(reference) = self.arena().type_data(source) else {
            return source;
        };
        let rebuilt = if let Some(target) = reference.target {
            Ty::type_reference_for_symbol(
                self.arena(),
                reference.name,
                target,
                type_arguments,
                display_type_argument_count,
            )
        } else {
            Ty::type_reference_with_display_type_argument_count(
                self.arena(),
                reference.name,
                type_arguments,
                display_type_argument_count,
            )
        };
        self.copy_type_alias_metadata(source, rebuilt);
        rebuilt
    }

    fn get_type_from_property_signature_annotation(
        &self,
        program_id: ProgramId,
        type_annotation: &'a TSTypeAnnotation<'a>,
    ) -> Ty<'a> {
        if let TSType::TSTypeReference(reference) = &type_annotation.type_annotation
            && let Some(expanded) =
                self.get_flat_mapped_intersection_alias_reference(program_id, reference, 0)
        {
            return expanded;
        }

        let ty = self.get_type_from_ts_type(program_id, &type_annotation.type_annotation);
        let ty = self.with_implicit_type_arguments_visible(ty);
        self.get_apparent_property_signature_type(program_id, ty, 0)
    }

    fn get_apparent_property_signature_type(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::TypeReference(reference)
                if self.is_conditional_type_alias_reference(program_id, reference) =>
            {
                self.get_conditional_type_alias_reference_type(program_id, reference)
                    .map(|(expanded_program_id, expanded)| {
                        let expanded =
                            if matches!(self.arena().type_data(expanded), TypeData::Conditional(_))
                            {
                                self.apparent_type_for_conditional_match(
                                    expanded_program_id,
                                    expanded,
                                    depth + 1,
                                )
                            } else {
                                expanded
                            };
                        if matches!(self.arena().type_data(expanded), TypeData::Conditional(_)) {
                            ty
                        } else {
                            self.get_apparent_property_signature_type(
                                expanded_program_id,
                                expanded,
                                depth + 1,
                            )
                        }
                    })
                    .unwrap_or(ty)
            }
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union.types.iter().map(|ty| {
                    self.get_apparent_property_signature_type(program_id, *ty, depth + 1)
                }),
            ),
            _ => ty,
        }
    }

    fn get_type_from_ts_tuple_element(
        &self,
        program_id: ProgramId,
        element: &'a TSTupleElement<'a>,
    ) -> TupleElement<'a> {
        match element {
            TSTupleElement::TSRestType(rest) => {
                let ty = match &rest.type_annotation {
                    TSType::TSNamedTupleMember(named) => {
                        self.get_type_from_ts_named_tuple_member(program_id, named)
                    }
                    type_annotation => self.get_type_from_ts_type(program_id, type_annotation),
                };
                if self.is_active_unresolved_type_alias(ty) {
                    TupleElement::Rest(ty)
                } else {
                    TupleElement::Rest(
                        self.get_expanded_type_alias_reference_type(program_id, ty, 0)
                            .map_or(ty, |(_, expanded)| expanded),
                    )
                }
            }
            TSTupleElement::TSOptionalType(optional) => TupleElement::Optional(
                self.get_type_from_ts_type(program_id, &optional.type_annotation)
                    .or_undefined(self.arena()),
            ),
            TSTupleElement::TSNamedTupleMember(named) => {
                let element = self.get_type_from_ts_tuple_element(program_id, &named.element_type);
                if named.optional {
                    match element {
                        TupleElement::Regular(ty) | TupleElement::Optional(ty) => {
                            TupleElement::Optional(ty.or_undefined(self.arena()))
                        }
                        TupleElement::Rest(ty) => TupleElement::Rest(ty),
                    }
                } else {
                    element
                }
            }
            _ => TupleElement::Regular(match element.as_ts_type() {
                Some(ts_type) => self.get_type_from_ts_type(program_id, ts_type),
                None => Ty::none(),
            }),
        }
    }

    fn get_type_from_ts_named_tuple_member(
        &self,
        program_id: ProgramId,
        named: &'a TSNamedTupleMember<'a>,
    ) -> Ty<'a> {
        let element = self.get_type_from_ts_tuple_element(program_id, &named.element_type);
        if named.optional {
            match element {
                TupleElement::Regular(ty) | TupleElement::Optional(ty) => {
                    ty.or_undefined(self.arena())
                }
                TupleElement::Rest(ty) => ty,
            }
        } else {
            element.ty()
        }
    }

    fn get_ts_tuple_element_label(element: &TSTupleElement<'a>) -> Option<&'a str> {
        match element {
            TSTupleElement::TSNamedTupleMember(named) => Some(named.label.name.as_str()),
            TSTupleElement::TSRestType(rest) => match &rest.type_annotation {
                TSType::TSNamedTupleMember(named) => Some(named.label.name.as_str()),
                _ => None,
            },
            _ => None,
        }
    }

    fn is_late_bound_type_literal_member(member: &TSSignature<'_>) -> bool {
        match member {
            TSSignature::TSPropertySignature(property) => {
                property.computed && matches!(property.key, PropertyKey::Identifier(_))
            }
            TSSignature::TSMethodSignature(method) => {
                method.computed && matches!(method.key, PropertyKey::Identifier(_))
            }
            _ => false,
        }
    }

    /// Resolve a TypeScript type node, using symbols for references that need checker state.
    fn get_type_from_ts_type(&self, program_id: ProgramId, ty: &'a TSType<'a>) -> Ty<'a> {
        let depth = &self.ts_type_resolution_depth;
        let current = depth.get();
        if current >= TS_TYPE_RESOLUTION_MAX_DEPTH {
            return Ty::error(self.arena(), TypeErrorKind::TypeResolutionDepthExceeded);
        }

        depth.set(current + 1);
        let result = self.get_type_from_ts_type_inner(program_id, ty);
        depth.set(current);
        result
    }

    fn get_type_from_ts_type_inner(&self, program_id: ProgramId, ty: &'a TSType<'a>) -> Ty<'a> {
        match ty {
            TSType::TSNumberKeyword(_) => Ty::number(),
            TSType::TSStringKeyword(_) => Ty::string(),
            TSType::TSBooleanKeyword(_) => Ty::boolean(),
            TSType::TSBigIntKeyword(_) => Ty::bigint(),
            TSType::TSSymbolKeyword(_) => Ty::symbol(),
            TSType::TSUndefinedKeyword(_) => Ty::undefined(),
            TSType::TSNullKeyword(_) => Ty::null(),
            TSType::TSAnyKeyword(_) => Ty::any(),
            TSType::TSUnknownKeyword(_) => Ty::unknown(),
            TSType::TSVoidKeyword(_) => Ty::void(),
            TSType::TSNeverKeyword(_) => Ty::never(),
            TSType::TSObjectKeyword(_) => Ty::primitive_object(),
            TSType::TSThisType(_) => Ty::this(),
            TSType::TSTypeLiteral(type_literal) => Ty::object_with_signatures_and_index_infos(
                self.arena(),
                type_literal
                    .members
                    .iter()
                    .filter(|member| !Self::is_late_bound_type_literal_member(member))
                    .chain(
                        type_literal
                            .members
                            .iter()
                            .filter(|member| Self::is_late_bound_type_literal_member(member)),
                    )
                    .filter_map(|member| match member {
                        TSSignature::TSPropertySignature(property) => {
                            let name = self.resolved_property_key_name(program_id, &property.key)?;
                            let ty = property.type_annotation.as_deref().map_or_else(
                                Ty::any,
                                |annotation| {
                                    self.get_type_from_ts_type(
                                        program_id,
                                        &annotation.type_annotation,
                                    )
                                },
                            );
                            Some(TyProperty {
                                name,
                                ty,
                                computed: property.computed,
                                optional: property.optional,
                                method: false,
                                readonly: property.readonly,
                            })
                        }
                        TSSignature::TSMethodSignature(method) => {
                            let name = self.resolved_property_key_name(program_id, &method.key)?;
                            if let Some(ty) =
                                self.get_type_of_ts_accessor_signature(program_id, method)
                            {
                                let has_getter = type_literal.members.iter().any(|member| {
                                    matches!(
                                        member,
                                        TSSignature::TSMethodSignature(candidate)
                                            if candidate.kind == TSMethodSignatureKind::Get
                                                && property_key_name_str(&candidate.key) == Some(name)
                                    )
                                });
                                if method.kind == TSMethodSignatureKind::Set && has_getter {
                                    return None;
                                }
                                let has_setter = type_literal.members.iter().any(|member| {
                                    matches!(
                                        member,
                                        TSSignature::TSMethodSignature(candidate)
                                            if candidate.kind == TSMethodSignatureKind::Set
                                                && property_key_name_str(&candidate.key) == Some(name)
                                    )
                                });
                                return Some(TyProperty {
                                    name,
                                    ty,
                                    computed: method.computed,
                                    optional: method.optional,
                                    method: false,
                                    readonly: !has_setter,
                                });
                            }

                            let parameters = self.function_type_parameters(
                                program_id,
                                method.this_param.as_deref(),
                                method.params.as_ref(),
                            );
                            let (return_type, type_predicate) = self
                                .return_type_and_type_predicate_from_annotation(
                                    program_id,
                                    &parameters,
                                    method.return_type.as_deref(),
                                );
                            let ty = Ty::function_with_type_predicate(
                                self.arena(),
                                self.type_parameters_from_declaration(
                                    program_id,
                                    method.type_parameters.as_deref(),
                                ),
                                parameters,
                                return_type,
                                type_predicate,
                            );
                            Some(TyProperty {
                                name,
                                ty,
                                computed: method.computed,
                                optional: method.optional,
                                method: true,
                                readonly: false,
                            })
                        }
                        _ => None,
                    }),
                type_literal.members.iter().filter_map(|member| {
                    self.signature_from_type_literal_signature(program_id, member)
                }),
                type_literal
                    .members
                    .iter()
                    .filter_map(|member| {
                        let TSSignature::TSIndexSignature(index_signature) = member else {
                            return None;
                        };
                        if index_signature.parameters.len() != 1 {
                            return None;
                        }
                        Some(index_signature.parameters.iter().map(|index_sig_name| {
                            IndexInfo::new(
                                index_sig_name.name.as_str(),
                                self.get_type_from_ts_type_annotation(
                                    program_id,
                                    Some(&index_sig_name.type_annotation),
                                ),
                                self.get_type_from_ts_type_annotation(
                                    program_id,
                                    Some(&index_signature.type_annotation),
                                ),
                                index_signature.readonly,
                            )
                        }))
                    })
                    .flatten(),
            ),
            TSType::TSArrayType(array) => Ty::array(
                self.arena(),
                self.get_type_from_ts_type(program_id, &array.element_type),
            ),
            TSType::TSTypeReference(reference) => {
                self.get_type_from_ts_type_reference(program_id, reference)
            }
            TSType::TSTypeQuery(query) => self.get_type_from_ts_type_query(program_id, query),
            TSType::TSParenthesizedType(parenthesized) => {
                self.get_type_from_ts_type(program_id, &parenthesized.type_annotation)
            }
            TSType::TSTemplateLiteralType(template_literal) => self.get_template_literal_type(
                program_id,
                template_literal
                    .quasis
                    .iter()
                    .map(|q| TemplateLiteralElement {
                        value: q.value.raw.as_str(),
                    }),
                template_literal
                    .types
                    .iter()
                    .map(|ty| self.get_type_from_ts_type(program_id, ty)),
            ),
            TSType::TSIntersectionType(intersection_type) => Ty::intersection(
                self.arena(),
                intersection_type
                    .types
                    .iter()
                    .map(|ty| self.get_type_from_ts_type(program_id, ty)),
            ),
            TSType::TSUnionType(union_type) => Ty::union(
                self.arena(),
                union_type
                    .types
                    .iter()
                    .map(|ty| self.get_type_from_ts_type(program_id, ty)),
            ),
            TSType::TSFunctionType(function) => {
                let previous_hide_implicit_type_argument_display =
                    self.hide_implicit_type_argument_display.replace(true);
                let parameters = self.function_type_parameters(
                    program_id,
                    function.this_param.as_deref(),
                    function.params.as_ref(),
                );
                let (return_type, type_predicate) = self
                    .return_type_and_type_predicate_from_annotation(
                        program_id,
                        &parameters,
                        Some(&function.return_type),
                    );
                 self.hide_implicit_type_argument_display
                    .set(previous_hide_implicit_type_argument_display);
                Ty::function_with_type_predicate(
                    self.arena(),
                    self.type_parameters_from_declaration(
                        program_id,
                        function.type_parameters.as_deref(),
                    ),
                    parameters,
                    return_type,
                    type_predicate,
                )
            }
            TSType::TSLiteralType(literal) => match &literal.literal {
                TSLiteral::BooleanLiteral(boolean_literal) => {
                    Ty::boolean_literal(boolean_literal.value)
                }
                TSLiteral::NumericLiteral(numeric_literal) => {
                    Ty::number_literal_from_ast(self.arena(), numeric_literal, false)
                }
                TSLiteral::StringLiteral(string_literal) => {
                    Ty::string_literal(self.arena(), string_literal.value.as_str())
                }
                TSLiteral::BigIntLiteral(bigint_literal) => {
                    Ty::bigint_literal(self.arena(), bigint_literal.value.as_str())
                }
                TSLiteral::TemplateLiteral(template_literal) => {
                    let quasis = template_literal
                        .quasis
                        .iter()
                        .map(|q| TemplateLiteralElement {
                            value: q.value.raw.as_str(),
                        });
                    let expressions = template_literal.expressions.iter().map(|expr| {
                        self.get_type_of_expression_with_node(
                            program_id,
                            expr,
                            None,
                            GetTypeFlags::NONE,
                        )
                    });
                    self.get_template_literal_type(program_id, quasis, expressions)
                }
                TSLiteral::UnaryExpression(unary_expression) => {
                    let Expression::NumericLiteral(numeric_literal) = &unary_expression.argument
                    else {
                        return Ty::none();
                    };
                    match unary_expression.operator {
                        UnaryOperator::UnaryNegation => Ty::number_literal_from_ast(
                            self.arena(),
                            numeric_literal,
                            true,
                        ),
                        UnaryOperator::UnaryPlus => Ty::number_literal_from_ast(
                            self.arena(),
                            numeric_literal,
                            false,
                        ),
                        _ => Ty::none(),
                    }
                }
            },
            TSType::TSTupleType(tuple_type) => Ty::tuple_with_labels(
                self.arena(),
                tuple_type
                    .element_types
                    .iter()
                    .map(|element| self.get_type_from_ts_tuple_element(program_id, element))
                    .collect(),
                tuple_type
                    .element_types
                    .iter()
                    .map(Self::get_ts_tuple_element_label)
                    .collect(),
                false,
            ),
            TSType::TSTypeOperatorType(operator) => match operator.operator {
                TSTypeOperatorOperator::Keyof => Ty::keyof(
                    self.arena(),
                    self.get_type_from_ts_type(program_id, &operator.type_annotation),
                ),
                TSTypeOperatorOperator::Unique
                    if matches!(operator.type_annotation, TSType::TSSymbolKeyword(_)) =>
                {
                    Ty::unique_symbol(self.arena(), None)
                }
                TSTypeOperatorOperator::Readonly => {
                    let inner = self.get_type_from_ts_type(program_id, &operator.type_annotation);
                    match self.arena().type_data(inner) {
                        TypeData::Array(array) => {
                            Ty::readonly_array(self.arena(), array.element_type)
                        }
                        TypeData::Tuple(tuple) => Ty::tuple_with_labels(
                            self.arena(),
                            tuple.elements.iter().copied().collect(),
                            tuple.labels.iter().copied().collect(),
                            true,
                        ),
                        _ => inner,
                    }
                }
                TSTypeOperatorOperator::Unique => Ty::none(),
            },
            TSType::TSIndexedAccessType(indexed_access) => {
                let object_type =
                    self.get_type_from_ts_type(program_id, &indexed_access.object_type);
                let index_type = self.get_type_from_ts_type(program_id, &indexed_access.index_type);
                let lookup_index_type = self.get_type_from_ts_type_expanding_top_level_aliases(
                    program_id,
                    &indexed_access.index_type,
                );
                match self.resolve_indexed_access_type(
                    program_id,
                    None,
                    object_type,
                    lookup_index_type,
                ) {
                    IndexedAccessResolution::Resolved(ty) => ty,
                    IndexedAccessResolution::Deferred | IndexedAccessResolution::Missing => {
                        Ty::indexed_access(self.arena(), object_type, index_type)
                    }
                }
            }
            TSType::TSConditionalType(conditional) => {
                let source_check_type =
                    self.get_type_from_ts_type(program_id, &conditional.check_type);
                let contains_infer = ts_type_contains_infer(&conditional.extends_type);
                let source_extends_type =
                    self.get_type_from_ts_type(program_id, &conditional.extends_type);
                let match_extends_type = if contains_infer {
                    self.get_type_from_ts_type_expanding_top_level_aliases(
                        program_id,
                        &conditional.extends_type,
                    )
                } else {
                    source_extends_type
                };
                let match_check_type = if contains_infer {
                    self.apparent_type_for_conditional_match(program_id, source_check_type, 0)
                } else if matches!(
                    self.arena().type_data(source_check_type),
                    TypeData::IndexedAccess(_)
                ) {
                    self.expand_type_at_use(program_id, source_check_type, 0)
                } else {
                    source_check_type
                };
                let true_type = self.get_type_from_ts_type(program_id, &conditional.true_type);
                let false_type = self.get_type_from_ts_type(program_id, &conditional.false_type);
                let is_distributive = matches!(
                    conditional.check_type,
                    TSType::TSTypeReference(ref reference) if reference.type_arguments.is_none()
                );
                let ty = self.conditional_type(
                    match_check_type,
                    match_extends_type,
                    true_type,
                    false_type,
                    is_distributive,
                );
                if contains_infer && matches!(self.arena().type_data(ty), TypeData::Conditional(_))
                {
                    self.arena()
                        .alloc_type(TypeData::Conditional(self.arena().alloc(TyConditional {
                            check_type: source_check_type,
                            extends_type: source_extends_type,
                            true_type,
                            false_type,
                            is_distributive,
                        })))
                } else {
                    ty
                }
            }
            TSType::TSInferType(infer) => Ty::infer(
                self.arena(),
                self.type_parameter_from_ts_type_parameter(program_id, &infer.type_parameter),
            ),
            TSType::TSMappedType(mapped) => self.get_type_from_ts_mapped_type(program_id, mapped),
            TSType::TSTypePredicate(predicate) => type_predicate_return_type(predicate.asserts),
            TSType::TSIntrinsicKeyword(_) => Ty::type_reference(
                self.arena(),
                "intrinsic",
                std::iter::empty(),
            ),
            TSType::TSConstructorType(constructor) => {
                let parameters = self.function_type_parameters(
                    program_id,
                    None,
                    constructor.params.as_ref(),
                );
                let (return_type, type_predicate) =
                    self.return_type_and_type_predicate_from_annotation(
                        program_id,
                        &parameters,
                        Some(&constructor.return_type),
                    );
                let signature = Signature::new(
                    SignatureKind::Construct,
                    Ty::function_with_type_predicate(
                        self.arena(),
                        self.type_parameters_from_declaration(
                            program_id,
                            constructor.type_parameters.as_deref(),
                        ),
                        parameters,
                        return_type,
                        type_predicate,
                    ),
                );
                Ty::constructor_type(self.arena(), signature)
            }
            TSType::TSImportType(import_type) => {
                self.get_type_from_ts_import_type(program_id, import_type)
            }
            TSType::TSNamedTupleMember(named) => {
                self.get_type_from_ts_named_tuple_member(program_id, named)
            }
            TSType::JSDocNullableType(_)
            | TSType::JSDocNonNullableType(_)
            | TSType::JSDocUnknownType(_) => {
                // TODO(completeness): We are not currently handling JSDoc.
                Ty::error(self.arena(), TypeErrorKind::UnsupportedType)
            }
        }
    }

    fn get_type_from_ts_import_type(
        &self,
        program_id: ProgramId,
        import_type: &'a TSImportType<'a>,
    ) -> Ty<'a> {
        let source = import_type.source.value.as_str();
        let Some(imported_program_id) = self.store.resolved_module(program_id, source) else {
            return Ty::error(self.arena(), TypeErrorKind::UnresolvedImport);
        };

        let module_type = self.get_module_namespace_type(imported_program_id, source);
        let type_arguments = import_type
            .type_arguments
            .as_ref()
            .into_iter()
            .flat_map(|type_arguments| type_arguments.params.iter())
            .map(|ty| self.get_type_argument_from_ts_type(program_id, ty))
            .collect::<Vec<_>>();

        let Some(qualifier) = import_type.qualifier.as_ref() else {
            let name = self.arena().str(&format!("import(\"{source}\")"));
            return Ty::type_query(self.arena(), name, module_type, type_arguments);
        };

        let ty = self.get_type_from_ts_import_type_qualifier(
            imported_program_id,
            module_type,
            qualifier,
            &type_arguments,
        );
        if type_arguments.is_empty() {
            ty
        } else {
            self.instantiate_type_query_type(program_id, ty, &type_arguments)
        }
    }

    fn get_type_of_ts_import_type_qualifier_identifier(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        name: &str,
    ) -> Ty<'a> {
        let Some(import_type) = self
            .nodes(program_id)
            .ancestor_kinds(node_id)
            .find_map(|kind| match kind {
                AstKind::TSImportType(import_type) => Some(import_type),
                _ => None,
            })
        else {
            return Ty::error(self.arena(), TypeErrorKind::UnresolvedImport);
        };
        let Some(imported_program_id) = self
            .store
            .resolved_module(program_id, import_type.source.value.as_str())
        else {
            return Ty::error(self.arena(), TypeErrorKind::UnresolvedImport);
        };
        let Some(symbol) = self.get_root_symbol(imported_program_id, name) else {
            return Ty::error(self.arena(), TypeErrorKind::UnresolvedSymbol);
        };
        self.get_type_of_ts_import_type_symbol(symbol, &[])
            .unwrap_or_else(|| Ty::error(self.arena(), TypeErrorKind::UnresolvedType))
    }

    fn get_type_from_ts_import_type_qualifier(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        qualifier: &TSImportTypeQualifier<'a>,
        type_arguments: &[Ty<'a>],
    ) -> Ty<'a> {
        match qualifier {
            TSImportTypeQualifier::Identifier(identifier) => self
                .get_type_of_ts_import_type_member(
                    program_id,
                    object_type,
                    identifier.name.as_str(),
                    type_arguments,
                )
                .unwrap_or_else(|| Ty::error(self.arena(), TypeErrorKind::UnresolvedMember)),
            TSImportTypeQualifier::QualifiedName(qualified) => {
                let object_type = self.get_type_from_ts_import_type_qualifier(
                    program_id,
                    object_type,
                    &qualified.left,
                    &[],
                );
                self.get_type_of_ts_import_type_member(
                    program_id,
                    object_type,
                    qualified.right.name.as_str(),
                    type_arguments,
                )
                .unwrap_or_else(|| Ty::error(self.arena(), TypeErrorKind::UnresolvedMember))
            }
        }
    }

    fn get_type_of_ts_import_type_member(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        member_name: &str,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        if let TypeData::TypeQuery(query) = self.arena().type_data(object_type)
            && let Some(namespace_symbol) = self.get_root_symbol(program_id, query.name)
            && let Some(member_symbol) =
                self.get_ts_import_type_namespace_member(namespace_symbol, member_name)
        {
            return self.get_type_of_ts_import_type_symbol(member_symbol, type_arguments);
        }

        if let Some(symbol) = self.get_root_symbol(program_id, member_name)
            && let Some(ty) = self.get_type_of_ts_import_type_symbol(symbol, type_arguments)
        {
            return Some(ty);
        }

        self.get_property_type_of_structural_type(program_id, object_type, member_name)
    }

    fn get_ts_import_type_namespace_member(
        &self,
        namespace_symbol: SymbolRef,
        member_name: &str,
    ) -> Option<SymbolRef> {
        let mut declaration = self
            .semantic(namespace_symbol.program_id)
            .scoping()
            .symbol_declaration(namespace_symbol.symbol_id);
        let module = loop {
            match self.nodes(namespace_symbol.program_id).kind(declaration) {
                AstKind::TSModuleDeclaration(module) => break module,
                AstKind::ExportNamedDeclaration(export) => {
                    declaration = export.declaration.as_ref()?.node_id();
                }
                AstKind::BindingIdentifier(_) => {
                    declaration = self
                        .nodes(namespace_symbol.program_id)
                        .parent_id(declaration);
                }
                _ => return None,
            }
        };
        let scope_id = module.scope_id.get()?;
        let member_symbol = self
            .semantic(namespace_symbol.program_id)
            .scoping()
            .get_binding(scope_id, Ident::from(member_name))?;
        Some(SymbolRef::new(namespace_symbol.program_id, member_symbol))
    }

    fn get_type_of_ts_import_type_symbol(
        &self,
        symbol: SymbolRef,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.get_type_of_ts_import_type_declaration(symbol, declaration, type_arguments)
    }

    fn get_type_of_ts_import_type_declaration(
        &self,
        symbol: SymbolRef,
        declaration: NodeId,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        match self.nodes(symbol.program_id).kind(declaration) {
            AstKind::ExportNamedDeclaration(export) => self.get_type_of_ts_import_type_declaration(
                symbol,
                export.declaration.as_ref()?.node_id(),
                type_arguments,
            ),
            AstKind::TSTypeAliasDeclaration(alias) => {
                self.get_expanded_type_alias_declaration(
                    symbol.program_id,
                    declaration,
                    type_arguments,
                    0,
                )
                .or_else(|| Some(self.get_type_of_type_alias_declaration(symbol.program_id, alias)))
            }
            AstKind::BindingIdentifier(_) => self.get_type_of_ts_import_type_declaration(
                symbol,
                self.nodes(symbol.program_id).parent_id(declaration),
                type_arguments,
            ),
            AstKind::TSInterfaceDeclaration(_)
            | AstKind::Class(_)
            | AstKind::TSEnumDeclaration(_) => {
                let name = self
                    .semantic(symbol.program_id)
                    .scoping()
                    .symbol_name(symbol.symbol_id)
                    .to_string();
                let name = self.arena().str(&name);
                let mut type_arguments = type_arguments.to_vec();
                self.fill_default_type_arguments(symbol.program_id, name, &mut type_arguments);
                let display_type_argument_count = type_arguments.len();
                Some(Ty::type_reference_for_symbol(
                    self.arena(),
                    name,
                    symbol,
                    type_arguments,
                    display_type_argument_count,
                ))
            }
            AstKind::TSModuleDeclaration(module) => {
                let TSModuleDeclarationName::Identifier(identifier) = &module.id else {
                    return None;
                };
                Some(Ty::type_query(
                    self.arena(),
                    identifier.name.as_str(),
                    Ty::any(),
                    std::iter::empty(),
                ))
            }
            _ => None,
        }
    }

    fn get_type_from_ts_mapped_type(
        &self,
        program_id: ProgramId,
        mapped: &'a TSMappedType<'a>,
    ) -> Ty<'a> {
        let constraint = self.get_type_from_ts_type(program_id, &mapped.constraint);
        let name_type = mapped
            .name_type
            .as_ref()
            .map(|name_ty| self.get_type_from_ts_type(program_id, name_ty));
        let optional = MappedModifier::from_ast(mapped.optional);
        let template = mapped
            .type_annotation
            .as_ref()
            .map_or_else(Ty::any, |ty| self.get_type_from_ts_type(program_id, ty));
        let template = if matches!(optional, MappedModifier::True | MappedModifier::Plus) {
            template.or_undefined(self.arena())
        } else {
            template
        };

        Ty::mapped(
            self.arena(),
            self.arena().str(&mapped.key.name),
            constraint,
            name_type,
            template,
            optional,
            MappedModifier::from_ast(mapped.readonly),
        )
    }

    /// Resolve `typeof Foo` type queries and apply query type arguments when present.
    /// Mirrors typescript-go: resolve the entity name as a value-meaning symbol, then
    /// wrap the resulting type in `Ty::TypeQuery` so display and downstream consumers
    /// can recover the queried name. When explicit type arguments are present we
    /// eagerly expand the wrapper into the substituted shape (e.g. a class typeof
    /// becomes a synthetic constructor object) so generic call/intersection sites work.
    fn get_type_from_ts_type_query(
        &self,
        program_id: ProgramId,
        query: &'a TSTypeQuery<'a>,
    ) -> Ty<'a> {
        let Some(name) = ts_type_query_expr_name_to_str(self.arena(), &query.expr_name) else {
            return Ty::error(self.arena(), TypeErrorKind::UnsupportedType);
        };

        let resolved = match &query.expr_name {
            TSTypeQueryExprName::IdentifierReference(identifier) => {
                let symbol = self
                    .symbol_for_identifier_reference(program_id, identifier)
                    .or_else(|| self.get_value_symbol_for_name(program_id, name));
                match symbol {
                    Some(symbol) => self.get_type_of_symbol(symbol),
                    None if identifier.name == GLOBAL_THIS_IDENT => return Ty::global_this(),
                    None => Ty::error(self.arena(), TypeErrorKind::UnresolvedSymbol),
                }
            }
            // TODO(correctness): resolve qualified-name and `this` typeof targets to a
            // real symbol so `resolved` is meaningful instead of `Ty::any`.
            _ => Ty::error(self.arena(), TypeErrorKind::UnsupportedType),
        };

        let type_arguments = query
            .type_arguments
            .as_ref()
            .into_iter()
            .flat_map(|type_arguments| {
                type_arguments
                    .params
                    .iter()
                    .map(|ty| self.get_type_from_ts_type(program_id, ty))
            })
            .collect::<Vec<_>>();

        if type_arguments.is_empty() {
            Ty::type_query(self.arena(), name, resolved, std::iter::empty())
        } else {
            self.instantiate_type_query_type(program_id, resolved, &type_arguments)
        }
    }

    pub(crate) fn get_type_of_type_alias_declaration(
        &self,
        program_id: ProgramId,
        alias: &'a oxc_ast::ast::TSTypeAliasDeclaration<'a>,
    ) -> Ty<'a> {
        if let TSType::TSTypeQuery(query) = &alias.type_annotation
            && let Some(name) = ts_type_query_expr_name_to_str(self.arena(), &query.expr_name)
        {
            let query_type = self.get_type_from_ts_type_query(program_id, query);
            if matches!(self.arena().type_data(query_type), TypeData::GlobalThis) {
                return query_type;
            }
            if let TypeData::TypeQuery(query) = self.arena().type_data(query_type)
                && matches!(
                    self.arena().type_data(query.resolved),
                    TypeData::UniqueSymbol(_)
                )
            {
                return query.resolved;
            }

            let type_arguments =
                query
                    .type_arguments
                    .as_ref()
                    .into_iter()
                    .flat_map(|type_arguments| {
                        type_arguments
                            .params
                            .iter()
                            .map(|ty| self.get_type_from_ts_type(program_id, ty))
                    });
            let resolved = match self.arena().type_data(query_type) {
                TypeData::TypeQuery(query) if query.resolved.is_error(self.arena()) => {
                    query.resolved
                }
                TypeData::Error(_) => query_type,
                _ => Ty::any(),
            };
            return Ty::type_query(self.arena(), name, resolved, type_arguments);
        }

        let ty = self
            .get_type_from_ts_type_expanding_top_level_aliases(program_id, &alias.type_annotation);
        self.expand_index_signature_alias_result(program_id, ty, 0)
    }

    fn get_type_from_ts_type_expanding_top_level_aliases(
        &self,
        program_id: ProgramId,
        ty: &'a TSType<'a>,
    ) -> Ty<'a> {
        self.get_type_from_ts_type_expanding_top_level_aliases_at_depth(program_id, ty, 0)
    }

    fn get_type_from_ts_type_expanding_top_level_aliases_at_depth(
        &self,
        program_id: ProgramId,
        ty: &'a TSType<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return self.get_type_from_ts_type(program_id, ty);
        }

        match ty {
            TSType::TSTypeReference(reference) => self
                .get_expanded_type_alias_reference(program_id, reference, depth + 1)
                .unwrap_or_else(|| self.get_type_from_ts_type_reference(program_id, reference)),
            TSType::TSUnionType(union_type) => Ty::union(
                self.arena(),
                union_type.types.iter().map(|ty| match ty {
                    TSType::TSTypeReference(reference) => self
                        .get_expanded_type_alias_reference(program_id, reference, depth + 1)
                        .filter(|expanded| {
                            expanded.is_transparent_type_alias_union_constituent(self.arena())
                        })
                        .unwrap_or_else(|| {
                            self.get_type_from_ts_type_reference(program_id, reference)
                        }),
                    TSType::TSParenthesizedType(parenthesized) => self
                        .get_type_from_ts_type_expanding_top_level_aliases_at_depth(
                            program_id,
                            &parenthesized.type_annotation,
                            depth + 1,
                        ),
                    _ => self.get_type_from_ts_type(program_id, ty),
                }),
            ),
            TSType::TSParenthesizedType(parenthesized) => self
                .get_type_from_ts_type_expanding_top_level_aliases_at_depth(
                    program_id,
                    &parenthesized.type_annotation,
                    depth + 1,
                ),
            _ => self.get_type_from_ts_type(program_id, ty),
        }
    }

    fn expand_index_signature_alias_result(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::TypeReference(_) => self
                .get_expanded_type_alias_reference_type(program_id, ty, depth + 1)
                .map(|(_, expanded)| expanded)
                .filter(|expanded| expanded.is_index_signature_object(self.arena()))
                .unwrap_or(ty),
            _ => ty,
        }
    }

    fn resolve_indexed_access_type(
        &self,
        program_id: ProgramId,
        node_id: Option<NodeId>,
        object_type: Ty<'a>,
        index_type: Ty<'a>,
    ) -> IndexedAccessResolution<'a> {
        if let Some(constraint) =
            self.concrete_index_type_constraint(program_id, node_id, index_type)
        {
            let constrained =
                self.resolve_indexed_access_type(program_id, None, object_type, constraint);
            if !matches!(constrained, IndexedAccessResolution::Missing) {
                return constrained;
            }
        }

        if matches!(
            self.arena().type_data(index_type),
            TypeData::TypeReference(reference) if reference.is_bare()
        ) {
            return IndexedAccessResolution::Deferred;
        }

        if let TypeData::Union(union) = self.arena().type_data(object_type) {
            let mut property_types = Vec::with_capacity(union.types.len());
            let mut has_deferred = false;
            for object_type in &union.types {
                match self.resolve_indexed_access_type(
                    program_id,
                    node_id,
                    *object_type,
                    index_type,
                ) {
                    IndexedAccessResolution::Resolved(ty) => property_types.push(ty),
                    IndexedAccessResolution::Deferred => {
                        has_deferred = true;
                        property_types.push(Ty::indexed_access(
                            self.arena(),
                            *object_type,
                            index_type,
                        ));
                    }
                    IndexedAccessResolution::Missing => {
                        return if self.is_generic_indexed_access(*object_type, index_type) {
                            IndexedAccessResolution::Deferred
                        } else {
                            IndexedAccessResolution::Missing
                        };
                    }
                }
            }
            return if has_deferred || !property_types.is_empty() {
                IndexedAccessResolution::Resolved(Ty::union(self.arena(), property_types))
            } else {
                IndexedAccessResolution::Missing
            };
        }

        if let TypeData::Array(array) = self.arena().type_data(object_type)
            && index_type.is_number_like(self.arena())
        {
            return IndexedAccessResolution::Resolved(array.element_type);
        }

        if let TypeData::Tuple(_) = self.arena().type_data(object_type)
            && let Some(index) = tuple_index_from_index_type(self.arena(), index_type)
        {
            return tuple_element_type_at_index(self.arena(), object_type, index).map_or(
                IndexedAccessResolution::Missing,
                IndexedAccessResolution::Resolved,
            );
        }

        match self.arena().type_data(index_type) {
            TypeData::Union(union) => {
                let mut property_types = Vec::with_capacity(union.types.len());
                let mut has_deferred = false;
                for index_type in &union.types {
                    match self.resolve_indexed_access_type(
                        program_id,
                        node_id,
                        object_type,
                        *index_type,
                    ) {
                        IndexedAccessResolution::Resolved(ty) => property_types.push(ty),
                        IndexedAccessResolution::Deferred => has_deferred = true,
                        IndexedAccessResolution::Missing => {
                            return IndexedAccessResolution::Missing;
                        }
                    }
                }
                if has_deferred {
                    IndexedAccessResolution::Deferred
                } else {
                    IndexedAccessResolution::Resolved(Ty::union(self.arena(), property_types))
                }
            }
            TypeData::UniqueSymbol(symbol) => {
                let property_type = symbol.name.and_then(|property_name| {
                    self.get_property_type_for_indexed_access_with_computed(
                        program_id,
                        object_type,
                        property_name,
                        true,
                    )
                });
                property_type.map_or_else(
                    || {
                        if self.is_generic_indexed_access(object_type, index_type) {
                            IndexedAccessResolution::Deferred
                        } else {
                            IndexedAccessResolution::Missing
                        }
                    },
                    IndexedAccessResolution::Resolved,
                )
            }
            _ => {
                if !matches!(
                    self.arena().type_data(index_type),
                    TypeData::String | TypeData::Number
                ) && let Some(property_name) =
                    index_type_to_property_name(self.arena(), index_type)
                    && let Some(property_type) = self.get_property_type_for_indexed_access(
                        program_id,
                        object_type,
                        property_name,
                    )
                {
                    return IndexedAccessResolution::Resolved(property_type);
                }
                if let Some(value_type) = self.get_index_signature_type_for_indexed_access(
                    program_id,
                    object_type,
                    index_type,
                    0,
                ) {
                    return IndexedAccessResolution::Resolved(value_type);
                }
                if self.is_generic_indexed_access(object_type, index_type) {
                    IndexedAccessResolution::Deferred
                } else {
                    IndexedAccessResolution::Missing
                }
            }
        }
    }

    fn get_index_signature_type_for_indexed_access(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        index_type: Ty<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }

        match self.arena().type_data(object_type) {
            TypeData::Object(object) => object
                .index_infos
                .iter()
                .find(|index_info| self.is_assignable_to(index_type, index_info.key_type))
                .map(|index_info| index_info.value_type),
            TypeData::TypeReference(reference)
                if reference.is_bare() && reference.target.is_none() =>
            {
                None
            }
            TypeData::TypeReference(reference) => self
                .get_index_signature_type_from_alias_reference(
                    program_id,
                    reference,
                    index_type,
                    depth + 1,
                )
                .or_else(|| {
                    self.get_expanded_type_alias_reference_type(program_id, object_type, depth + 1)
                        .and_then(|(expanded_program_id, expanded)| {
                            self.get_index_signature_type_for_indexed_access(
                                expanded_program_id,
                                expanded,
                                index_type,
                                depth + 1,
                            )
                        })
                }),
            TypeData::Union(union) => union
                .types
                .iter()
                .map(|ty| {
                    self.get_index_signature_type_for_indexed_access(
                        program_id,
                        *ty,
                        index_type,
                        depth + 1,
                    )
                })
                .collect::<Option<Vec<_>>>()
                .map(|types| Ty::union(self.arena(), types)),
            TypeData::Intersection(intersection) => intersection.types.iter().find_map(|ty| {
                self.get_index_signature_type_for_indexed_access(
                    program_id,
                    *ty,
                    index_type,
                    depth + 1,
                )
            }),
            TypeData::Mapped(mapped) => {
                let key_type = index_signature_key_types(self.arena(), mapped.constraint)?
                    .into_iter()
                    .find(|key_type| self.is_assignable_to(index_type, *key_type))?;
                let mapper = TypeMapper::single(
                    Ty::type_reference(self.arena(), mapped.key, std::iter::empty()),
                    key_type,
                );
                Some(self.instantiate_type(mapped.template, &mapper))
            }
            _ => None,
        }
    }

    fn get_index_signature_type_from_alias_reference(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
        index_type: Ty<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }
        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)?;
        let AstKind::TSTypeAliasDeclaration(alias) =
            self.nodes(symbol.program_id).kind(declaration)
        else {
            return None;
        };
        let alias_type = self.get_type_from_ts_type(symbol.program_id, &alias.type_annotation);
        let substitutions = self.type_parameter_substitutions_for_type_arguments(
            symbol.program_id,
            alias.type_parameters.as_deref(),
            reference.type_arguments.as_slice(),
        );
        let alias_type = self.instantiate_type(alias_type, &substitutions.to_mapper(self.arena()));
        self.get_index_signature_type_for_indexed_access(
            symbol.program_id,
            alias_type,
            index_type,
            depth + 1,
        )
    }

    fn get_property_type_for_indexed_access(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        self.get_property_type_for_indexed_access_with_computed(
            program_id,
            object_type,
            property_name,
            false,
        )
    }

    fn get_property_type_for_indexed_access_with_computed(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
        computed: bool,
    ) -> Option<Ty<'a>> {
        match self.arena().type_data(object_type) {
            TypeData::GlobalThis if !computed => {
                if property_name == GLOBAL_THIS_IDENT.as_str() {
                    Some(Ty::global_this())
                } else {
                    self.global_symbols
                        .global_this_value_symbol(property_name)
                        .map(|symbol| self.get_type_of_symbol(symbol))
                }
            }
            TypeData::Object(object) => object.properties.iter().find_map(|property| {
                if property.computed != computed || property.name != property_name {
                    return None;
                }
                Some(if property.optional {
                    property.ty.or_undefined(self.arena())
                } else {
                    property.ty
                })
            }),
            TypeData::Union(union) => {
                let property_types = union
                    .types
                    .iter()
                    .map(|ty| {
                        self.get_property_type_for_indexed_access_with_computed(
                            program_id,
                            *ty,
                            property_name,
                            computed,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(Ty::union(self.arena(), property_types))
            }
            TypeData::Intersection(intersection) => intersection.types.iter().find_map(|ty| {
                self.get_property_type_for_indexed_access_with_computed(
                    program_id,
                    *ty,
                    property_name,
                    computed,
                )
            }),
            TypeData::Tuple(tuple) if !computed => {
                self.get_property_type_of_tuple(object_type, tuple, property_name)
            }
            TypeData::Mapped(mapped) if !computed => {
                self.get_property_type_of_mapped_type(program_id, mapped, property_name, 0)
            }
            TypeData::TypeReference(reference) => self
                .get_expanded_type_alias_reference_type(program_id, object_type, 0)
                .and_then(|(expanded_program_id, expanded)| {
                    self.get_property_type_for_indexed_access_with_computed(
                        expanded_program_id,
                        expanded,
                        property_name,
                        computed,
                    )
                })
                .or_else(|| {
                    if computed {
                        None
                    } else {
                        self.get_property_type_of_interface_type(
                            program_id,
                            reference,
                            property_name,
                        )
                    }
                }),
            _ => None,
        }
    }

    fn get_property_type_of_mapped_type(
        &self,
        program_id: ProgramId,
        mapped: &TyMapped<'a>,
        property_name: &str,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }

        if let Some(properties) =
            self.properties_for_mapped_constraint(program_id, mapped.constraint, depth + 1)
            && !properties
                .iter()
                .any(|property| !property.computed && property.name == property_name)
        {
            return None;
        }

        let key_type = Ty::string_literal(self.arena(), self.arena().str(property_name));
        let mapper = TypeMapper::single(
            Ty::type_reference(self.arena(), mapped.key, std::iter::empty()),
            key_type,
        );

        if let Some(name_type) = mapped.name_type {
            let name_type = self.instantiate_type(name_type, &mapper);
            let name_type = self.expand_type_at_use(program_id, name_type, depth + 1);
            if name_type.is_never() {
                return None;
            }
            let remapped_name = index_type_to_property_name(self.arena(), name_type)?;
            if remapped_name != property_name {
                return None;
            }
        }

        let ty = self.instantiate_type(mapped.template, &mapper);
        let ty = self.expand_type_at_use(program_id, ty, depth + 1);
        let ty = self.expand_deferred_conditional_branches_at_use(program_id, ty, depth + 1);
        Some(
            if matches!(mapped.optional, MappedModifier::True | MappedModifier::Plus) {
                ty.or_undefined(self.arena())
            } else {
                ty
            },
        )
    }

    fn expand_deferred_conditional_branches_at_use(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::Conditional(conditional) => {
                self.arena()
                    .alloc_type(TypeData::Conditional(self.arena().alloc(TyConditional {
                        check_type: conditional.check_type,
                        extends_type: conditional.extends_type,
                        true_type: self.expand_deferred_conditional_branch_at_use(
                            program_id,
                            conditional.true_type,
                            depth + 1,
                        ),
                        false_type: self.expand_deferred_conditional_branch_at_use(
                            program_id,
                            conditional.false_type,
                            depth + 1,
                        ),
                        is_distributive: conditional.is_distributive,
                    })))
            }
            _ => ty,
        }
    }

    fn expand_deferred_conditional_branch_at_use(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::TypeReference(reference) => {
                let type_arguments = reference
                    .type_arguments
                    .iter()
                    .map(|ty| self.expand_type_for_index_lookup(program_id, *ty, depth + 1))
                    .collect::<Vec<_>>();
                self.rebuild_type_reference_with_display_type_argument_count(
                    ty,
                    type_arguments,
                    reference.display_type_argument_count,
                )
            }
            _ => self.expand_type_for_index_lookup(program_id, ty, depth + 1),
        }
    }

    fn expand_type_at_use(&self, program_id: ProgramId, ty: Ty<'a>, depth: usize) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::TypeReference(_) => self
                .get_expanded_type_alias_reference_type(program_id, ty, depth + 1)
                .map(|(expanded_program_id, expanded)| {
                    self.expand_type_at_use(expanded_program_id, expanded, depth + 1)
                })
                .unwrap_or(ty),
            TypeData::IndexedAccess(indexed_access) => {
                let object_type =
                    self.expand_type_at_use(program_id, indexed_access.object_type, depth + 1);
                let index_type = indexed_access.index_type;
                let lookup_index_type =
                    self.expand_type_for_index_lookup(program_id, index_type, depth + 1);
                match self.resolve_indexed_access_type(
                    program_id,
                    None,
                    object_type,
                    lookup_index_type,
                ) {
                    IndexedAccessResolution::Resolved(resolved) => {
                        self.expand_type_at_use(program_id, resolved, depth + 1)
                    }
                    IndexedAccessResolution::Deferred | IndexedAccessResolution::Missing => {
                        Ty::indexed_access(self.arena(), object_type, index_type)
                    }
                }
            }
            TypeData::Mapped(mapped) => self
                .expand_mapped_type(program_id, mapped, depth + 1)
                .unwrap_or(ty),
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.expand_type_at_use(program_id, *ty, depth + 1)),
            ),
            TypeData::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection
                    .types
                    .iter()
                    .map(|ty| self.expand_type_at_use(program_id, *ty, depth + 1)),
            ),
            TypeData::Conditional(conditional) => {
                let check_type =
                    self.expand_type_at_use(program_id, conditional.check_type, depth + 1);
                let extends_type =
                    self.expand_type_at_use(program_id, conditional.extends_type, depth + 1);
                let match_check_type = if self.infer_type_parameter_names(extends_type).is_empty() {
                    check_type
                } else {
                    self.apparent_type_for_conditional_match(program_id, check_type, depth + 1)
                };
                let ty = self.conditional_type(
                    match_check_type,
                    extends_type,
                    conditional.true_type,
                    conditional.false_type,
                    conditional.is_distributive,
                );
                if matches!(self.arena().type_data(ty), TypeData::Conditional(_)) {
                    if matches!(
                        self.arena().type_data(conditional.check_type),
                        TypeData::IndexedAccess(_)
                    ) {
                        self.arena()
                            .alloc_type(TypeData::Conditional(self.arena().alloc(TyConditional {
                                check_type,
                                extends_type,
                                true_type: conditional.true_type,
                                false_type: conditional.false_type,
                                is_distributive: conditional.is_distributive,
                            })))
                    } else {
                        ty
                    }
                } else {
                    self.expand_type_at_use(program_id, ty, depth + 1)
                }
            }
            TypeData::Keyof(keyof) => Ty::keyof(
                self.arena(),
                self.expand_type_at_use(program_id, keyof.target, depth + 1),
            ),
            _ => ty,
        }
    }

    fn normalize_instantiated_signature_return_type(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::IndexedAccess(_) => self.expand_type_at_use(program_id, ty, depth + 1),
            TypeData::TypeReference(reference) => {
                let type_arguments = reference
                    .type_arguments
                    .iter()
                    .map(|ty| match self.arena().type_data(*ty) {
                        TypeData::Mapped(mapped) => self
                            .materialize_homomorphic_mapped_type(program_id, mapped, depth + 1)
                            .unwrap_or(*ty),
                        _ => *ty,
                    })
                    .collect::<Vec<_>>();
                let reference_ty = self.rebuild_type_reference_with_display_type_argument_count(
                    ty,
                    type_arguments,
                    reference.display_type_argument_count,
                );
                if !self.is_empty_object_intersection_alias_reference(program_id, reference_ty) {
                    return reference_ty;
                }
                self.get_expanded_type_alias_reference_type(program_id, reference_ty, depth + 1)
                    .map(|(expanded_program_id, expanded)| {
                        self.normalize_instantiated_signature_return_type(
                            expanded_program_id,
                            expanded,
                            depth + 1,
                        )
                    })
                    .unwrap_or(reference_ty)
            }
            TypeData::Mapped(mapped) => self
                .materialize_homomorphic_mapped_type(program_id, mapped, depth + 1)
                .unwrap_or(ty),
            _ => ty,
        }
    }

    fn expand_type_for_index_lookup(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::TypeReference(reference) => {
                let expanded_arguments = reference
                    .type_arguments
                    .iter()
                    .map(|ty| self.expand_type_for_index_lookup(program_id, *ty, depth + 1))
                    .collect::<Vec<_>>();
                let reference_ty = self.rebuild_type_reference_with_display_type_argument_count(
                    ty,
                    expanded_arguments,
                    reference.display_type_argument_count,
                );
                self.get_expanded_type_alias_reference_type(program_id, reference_ty, depth + 1)
                    .map(|(expanded_program_id, expanded)| {
                        self.expand_type_for_index_lookup(expanded_program_id, expanded, depth + 1)
                    })
                    .unwrap_or(reference_ty)
            }
            TypeData::IndexedAccess(indexed_access) => {
                let object_type = self.expand_type_for_index_lookup(
                    program_id,
                    indexed_access.object_type,
                    depth + 1,
                );
                let index_type =
                    self.normalize_index_access_index_type_for_display(indexed_access.index_type);
                let lookup_index_type =
                    self.expand_type_for_index_lookup(program_id, index_type, depth + 1);
                match self.resolve_indexed_access_type(
                    program_id,
                    None,
                    object_type,
                    lookup_index_type,
                ) {
                    IndexedAccessResolution::Resolved(resolved) => {
                        self.expand_type_for_index_lookup(program_id, resolved, depth + 1)
                    }
                    IndexedAccessResolution::Deferred | IndexedAccessResolution::Missing => {
                        Ty::indexed_access(self.arena(), object_type, index_type)
                    }
                }
            }
            TypeData::Conditional(conditional) => {
                let check_type = self.expand_type_for_index_lookup(
                    program_id,
                    conditional.check_type,
                    depth + 1,
                );
                let extends_type = self.expand_type_for_index_lookup(
                    program_id,
                    conditional.extends_type,
                    depth + 1,
                );
                let ty = self.conditional_type(
                    check_type,
                    extends_type,
                    conditional.true_type,
                    conditional.false_type,
                    conditional.is_distributive,
                );
                if matches!(self.arena().type_data(ty), TypeData::Conditional(_)) {
                    ty
                } else {
                    self.expand_type_for_index_lookup(program_id, ty, depth + 1)
                }
            }
            TypeData::Keyof(keyof) => Ty::keyof(
                self.arena(),
                self.expand_type_for_index_lookup(program_id, keyof.target, depth + 1),
            ),
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.expand_type_for_index_lookup(program_id, *ty, depth + 1)),
            ),
            _ => ty,
        }
    }

    fn normalize_index_access_index_type_for_display(&self, ty: Ty<'a>) -> Ty<'a> {
        let TypeData::Intersection(intersection) = self.arena().type_data(ty) else {
            return ty;
        };
        let mut types = intersection.types.iter().copied().collect::<Vec<_>>();
        let mut changed = false;
        for i in 0..types.len() {
            if !matches!(
                self.arena().type_data(types[i]),
                TypeData::StringLiteral(_) | TypeData::NumberLiteral(_)
            ) {
                continue;
            }
            if let Some(keyof_offset) = types[i + 1..]
                .iter()
                .position(|ty| matches!(self.arena().type_data(*ty), TypeData::Keyof(_)))
            {
                types.swap(i, i + 1 + keyof_offset);
                changed = true;
            }
        }
        if changed {
            Ty::intersection(self.arena(), types)
        } else {
            ty
        }
    }

    fn expand_mapped_type(
        &self,
        program_id: ProgramId,
        mapped: &TyMapped<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if let Some(ty) = self.materialize_homomorphic_mapped_type(program_id, mapped, depth + 1) {
            return Some(ty);
        }

        if let Some(ty) = self.expand_index_signature_mapped_type(program_id, mapped, depth + 1) {
            return Some(ty);
        }

        let properties =
            self.properties_for_mapped_constraint(program_id, mapped.constraint, depth)?;
        let mut expanded = Vec::new();

        for property in properties {
            let key_type = Ty::string_literal(self.arena(), property.name);
            let mapper = TypeMapper::single(
                Ty::type_reference(self.arena(), mapped.key, std::iter::empty()),
                key_type,
            );
            let property_name = if let Some(name_type) = mapped.name_type {
                let name_type = self.instantiate_type(name_type, &mapper);
                let name_type = self.expand_type_at_use(program_id, name_type, depth + 1);
                if name_type.is_never() {
                    continue;
                }
                index_type_to_property_name(self.arena(), name_type)?
            } else {
                property.name
            };
            let ty = self.instantiate_type(mapped.template, &mapper);
            let ty = self.expand_type_at_use(program_id, ty, depth + 1);
            let ty = self.expand_deferred_conditional_branches_at_use(program_id, ty, depth + 1);
            expanded.push(TyProperty {
                name: property_name,
                ty,
                computed: false,
                optional: matches!(mapped.optional, MappedModifier::True | MappedModifier::Plus),
                method: false,
                readonly: property.readonly,
            });
        }

        Some(Ty::object(self.arena(), expanded))
    }

    fn materialize_homomorphic_mapped_type(
        &self,
        program_id: ProgramId,
        mapped: &TyMapped<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        let TypeData::Keyof(keyof) = self.arena().type_data(mapped.constraint) else {
            return None;
        };
        let target = self.expand_type_at_use(program_id, keyof.target, depth + 1);
        if mapped.name_type.is_some() {
            return None;
        }

        match self.arena().type_data(target) {
            TypeData::Array(array) => {
                let element_type = self.instantiate_mapped_type_template(
                    program_id,
                    mapped,
                    Ty::number(),
                    depth + 1,
                );
                Some(if self.mapped_readonly(mapped.readonly, array.readonly) {
                    Ty::readonly_array(self.arena(), element_type)
                } else {
                    Ty::array(self.arena(), element_type)
                })
            }
            TypeData::Tuple(tuple) => {
                let elements = tuple
                    .elements
                    .iter()
                    .enumerate()
                    .map(|(index, element)| {
                        let raw = self.arena().str(&index.to_string());
                        let key_type = Ty::number_literal(
                            self.arena(),
                            index as f64,
                            raw,
                            NumberBase::Decimal,
                        );
                        let element_type = self.instantiate_mapped_type_template(
                            program_id,
                            mapped,
                            key_type,
                            depth + 1,
                        );
                        self.materialize_mapped_tuple_element(
                            mapped.optional,
                            *element,
                            element_type,
                        )
                    })
                    .collect::<Vec<_>>();
                Some(Ty::tuple_with_labels(
                    self.arena(),
                    elements,
                    tuple.labels.iter().copied().collect(),
                    self.mapped_readonly(mapped.readonly, tuple.readonly),
                ))
            }
            _ => None,
        }
    }

    fn instantiate_mapped_type_template(
        &self,
        program_id: ProgramId,
        mapped: &TyMapped<'a>,
        key_type: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        let mapper = TypeMapper::single(
            Ty::type_reference(self.arena(), mapped.key, std::iter::empty()),
            key_type,
        );
        let template = self.instantiate_type(mapped.template, &mapper);
        self.expand_type_at_use(program_id, template, depth + 1)
    }

    fn materialize_mapped_tuple_element(
        &self,
        optional: MappedModifier,
        source: TupleElement<'a>,
        ty: Ty<'a>,
    ) -> TupleElement<'a> {
        match (optional, source) {
            (MappedModifier::True | MappedModifier::Plus, TupleElement::Rest(_)) => {
                TupleElement::Rest(ty)
            }
            (MappedModifier::True | MappedModifier::Plus, _) => TupleElement::Optional(ty),
            (MappedModifier::Minus, TupleElement::Rest(_)) => TupleElement::Rest(ty),
            (MappedModifier::Minus, _) => TupleElement::Regular(self.remove_undefined(ty)),
            (MappedModifier::None, TupleElement::Regular(_)) => TupleElement::Regular(ty),
            (MappedModifier::None, TupleElement::Rest(_)) => TupleElement::Rest(ty),
            (MappedModifier::None, TupleElement::Optional(_)) => TupleElement::Optional(ty),
        }
    }

    fn mapped_readonly(&self, modifier: MappedModifier, source_readonly: bool) -> bool {
        match modifier {
            MappedModifier::None => source_readonly,
            MappedModifier::True | MappedModifier::Plus => true,
            MappedModifier::Minus => false,
        }
    }

    fn expand_index_signature_mapped_type(
        &self,
        program_id: ProgramId,
        mapped: &TyMapped<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if mapped.name_type.is_some() {
            return None;
        }

        let key_types = index_signature_key_types(self.arena(), mapped.constraint)?;
        let index_infos = key_types.into_iter().map(|key_type| {
            let mapper = TypeMapper::single(
                Ty::type_reference(self.arena(), mapped.key, std::iter::empty()),
                key_type,
            );
            let ty = self.instantiate_type(mapped.template, &mapper);
            let ty = self.expand_index_signature_alias_result(program_id, ty, depth + 1);
            IndexInfo::synthetic(
                key_type,
                ty,
                matches!(mapped.readonly, MappedModifier::True | MappedModifier::Plus),
            )
        });

        Some(Ty::object_with_index_infos(self.arena(), [], index_infos))
    }

    fn properties_for_mapped_constraint(
        &self,
        program_id: ProgramId,
        constraint: Ty<'a>,
        depth: usize,
    ) -> Option<Vec<TyProperty<'a>>> {
        let TypeData::Keyof(keyof) = self.arena().type_data(constraint) else {
            return None;
        };
        self.properties_for_keyof_type(program_id, keyof.target, depth + 1)
    }

    fn properties_for_keyof_type(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Option<Vec<TyProperty<'a>>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }

        let ty = self.expand_type_at_use(program_id, ty, depth + 1);
        match self.arena().type_data(ty) {
            TypeData::Object(object) => Some(
                object
                    .properties
                    .iter()
                    .copied()
                    .filter(|property| !property.computed)
                    .collect(),
            ),
            TypeData::GlobalThis => {
                let mut symbols = self
                    .global_symbols
                    .global_this_value_symbols()
                    .collect::<Vec<_>>();
                symbols.sort_unstable_by_key(|(name, _)| *name);
                let mut properties = symbols
                    .into_iter()
                    .map(|(name, symbol)| {
                        Ty::property(self.arena().str(name), self.get_type_of_symbol(symbol))
                    })
                    .collect::<Vec<_>>();
                properties.push(Ty::property(
                    self.arena().str(GLOBAL_THIS_IDENT.as_str()),
                    Ty::global_this(),
                ));
                Some(properties)
            }
            TypeData::Intersection(intersection) => {
                let mut properties = Vec::new();
                for ty in &intersection.types {
                    for property in self.properties_for_keyof_type(program_id, *ty, depth + 1)? {
                        if !properties.iter().any(|existing: &TyProperty<'_>| {
                            existing.name == property.name && existing.computed == property.computed
                        }) {
                            properties.push(property);
                        }
                    }
                }
                Some(properties)
            }
            TypeData::TypeReference(_) => self
                .get_expanded_type_alias_reference_type(program_id, ty, depth + 1)
                .and_then(|(expanded_program_id, expanded)| {
                    self.properties_for_keyof_type(expanded_program_id, expanded, depth + 1)
                }),
            _ => None,
        }
    }

    fn get_expanded_type_alias_reference(
        &self,
        program_id: ProgramId,
        reference: &'a TSTypeReference<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        let name = ts_type_name_to_str(self.arena(), &reference.type_name);
        let mut type_arguments = self.type_arguments_from_reference(program_id, reference);

        self.fill_default_type_arguments(program_id, name, &mut type_arguments);
        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, name)?;
        if symbol.program_id != program_id {
            type_arguments = type_arguments
                .into_iter()
                .map(|ty| {
                    self.expand_type_alias_argument_for_foreign_declaration(
                        program_id,
                        ty,
                        depth + 1,
                    )
                })
                .collect::<Vec<_>>();
        }
        self.get_expanded_type_alias_declaration(
            symbol.program_id,
            declaration,
            &type_arguments,
            depth,
        )
    }

    fn expand_type_alias_argument_for_foreign_declaration(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::TypeReference(reference)
                if self.is_lib_type_reference(program_id, reference) =>
            {
                ty
            }
            TypeData::TypeReference(_) => self
                .get_expanded_type_alias_reference_type(program_id, ty, depth + 1)
                .map(|(expanded_program_id, expanded)| {
                    self.expand_type_at_use(expanded_program_id, expanded, depth + 1)
                })
                .unwrap_or(ty),
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union.types.iter().map(|ty| {
                    self.expand_type_alias_argument_for_foreign_declaration(
                        program_id,
                        *ty,
                        depth + 1,
                    )
                }),
            ),
            TypeData::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection.types.iter().map(|ty| {
                    self.expand_type_alias_argument_for_foreign_declaration(
                        program_id,
                        *ty,
                        depth + 1,
                    )
                }),
            ),
            TypeData::IndexedAccess(_) => self.expand_type_at_use(program_id, ty, depth + 1),
            _ => ty,
        }
    }

    fn is_lib_type_reference(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> bool {
        self.is_lib_type_name(program_id, reference.name)
    }

    fn is_lib_type_name(&self, program_id: ProgramId, type_name: &str) -> bool {
        self.get_type_symbol_for_name(program_id, type_name)
            .and_then(|symbol| self.store.entry(symbol.program_id))
            .is_some_and(program::ProgramEntry::is_lib)
    }

    fn get_flat_mapped_intersection_alias_reference(
        &self,
        program_id: ProgramId,
        reference: &'a TSTypeReference<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }

        let name = ts_type_name_to_str(self.arena(), &reference.type_name);
        let mut type_arguments = self.type_arguments_from_reference(program_id, reference);

        self.fill_default_type_arguments(program_id, name, &mut type_arguments);

        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, name)?;
        self.get_flat_mapped_intersection_alias_declaration(
            symbol.program_id,
            declaration,
            &type_arguments,
            depth + 1,
        )
    }

    fn get_flat_mapped_intersection_alias_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        type_arguments: &[Ty<'a>],
        depth: usize,
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias)
                if is_mapped_empty_object_intersection(&alias.type_annotation) =>
            {
                let substitutions = self.type_parameter_substitutions_for_type_arguments(
                    program_id,
                    alias.type_parameters.as_deref(),
                    type_arguments,
                );
                let ty = self.get_type_from_ts_type_expanding_top_level_aliases_at_depth(
                    program_id,
                    &alias.type_annotation,
                    depth + 1,
                );
                let ty = self.instantiate_type(ty, &substitutions.to_mapper(self.arena()));
                Some(self.expand_type_at_use(program_id, ty, depth + 1))
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_flat_mapped_intersection_alias_declaration(
                    program_id,
                    parent_id,
                    type_arguments,
                    depth + 1,
                )
            }
            _ => None,
        }
    }

    fn get_expanded_type_alias_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        type_arguments: &[Ty<'a>],
        depth: usize,
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias)
                if !matches!(alias.type_annotation, TSType::TSTypeQuery(_)) =>
            {
                let is_root_resolution = self.resolving_type_aliases.borrow().is_empty();
                if is_root_resolution {
                    self.type_instantiation_overflowed.set(false);
                    let previously_overflowed = self
                        .overflowed_type_alias_resolutions
                        .borrow()
                        .iter()
                        .any(|resolution| {
                            resolution.program_id == program_id
                                && resolution.declaration == declaration
                                && resolution.type_arguments.len() == type_arguments.len()
                                && resolution.type_arguments.iter().zip(type_arguments).all(
                                    |(cached, current)| {
                                        self.arena().type_from_id(*cached).is_some_and(|cached| {
                                            self.arena().is_type_identical_to(cached, *current)
                                        })
                                    },
                                )
                        });
                    if previously_overflowed {
                        return Some(Ty::error(
                            self.arena(),
                            TypeErrorKind::TypeAliasResolutionDepthExceeded,
                        ));
                    }
                }
                let key = TypeAliasResolution {
                    program_id,
                    declaration,
                    type_arguments: type_arguments.iter().map(|ty| ty.id()).collect(),
                };
                if let Some(ty) = self.type_alias_resolution_cache.borrow().get(&key) {
                    return Some(*ty);
                }
                {
                    let mut resolving_type_aliases = self.resolving_type_aliases.borrow_mut();
                    if resolving_type_aliases.len() >= TYPE_INSTANTIATION_MAX_DEPTH {
                        let error = Ty::error(
                            self.arena(),
                            TypeErrorKind::TypeAliasResolutionDepthExceeded,
                        );
                        let should_propagate =
                            resolving_type_aliases.first().is_some_and(|resolution| {
                                resolution.type_arguments.iter().all(|type_id| {
                                    self.arena()
                                        .type_from_id(*type_id)
                                        .is_some_and(|ty| !self.could_contain_type_variables(ty))
                                })
                            });
                        if should_propagate {
                            self.type_instantiation_overflowed.set(true);
                            let active_resolutions = resolving_type_aliases.clone();
                            drop(resolving_type_aliases);
                            if let Some(root_resolution) = active_resolutions.first() {
                                self.overflowed_type_alias_resolutions
                                    .borrow_mut()
                                    .push(root_resolution.clone());
                            }
                            let mut cache = self.type_alias_resolution_cache.borrow_mut();
                            for active_resolution in active_resolutions {
                                cache.insert(active_resolution, error);
                            }
                            cache.insert(key, error);
                        } else {
                            drop(resolving_type_aliases);
                            self.type_alias_resolution_cache
                                .borrow_mut()
                                .insert(key, error);
                        }
                        return Some(error);
                    }
                    if resolving_type_aliases.contains(&key) {
                        return None;
                    }
                    resolving_type_aliases.push(key.clone());
                }

                let substitutions = self.type_parameter_substitutions_for_type_arguments(
                    program_id,
                    alias.type_parameters.as_deref(),
                    type_arguments,
                );
                let ty = if matches!(alias.type_annotation, TSType::TSIntrinsicKeyword(_)) {
                    self.get_type_from_intrinsic_alias(
                        program_id,
                        alias.id.name.as_str(),
                        type_arguments,
                        depth + 1,
                    )
                } else {
                    self.get_type_from_ts_type_expanding_top_level_aliases_at_depth(
                        program_id,
                        &alias.type_annotation,
                        depth + 1,
                    )
                };
                let ty = self.instantiate_type(ty, &substitutions.to_mapper(self.arena()));
                let ty = if self.type_instantiation_overflowed.get() {
                    Ty::error(self.arena(), TypeErrorKind::TypeInstantiationDepthExceeded)
                } else {
                    self.expand_type_at_use(program_id, ty, depth + 1)
                };
                let ty = if self.type_instantiation_overflowed.get() {
                    Ty::error(self.arena(), TypeErrorKind::TypeInstantiationDepthExceeded)
                } else {
                    ty
                };

                self.resolving_type_aliases.borrow_mut().pop();
                if self.type_instantiation_overflowed.get() && ty.is_error(self.arena()) {
                    self.overflowed_type_alias_resolutions
                        .borrow_mut()
                        .push(key.clone());
                }
                self.type_alias_resolution_cache
                    .borrow_mut()
                    .insert(key, ty);
                if is_root_resolution {
                    self.type_instantiation_overflowed.set(false);
                }
                Some(ty)
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_expanded_type_alias_declaration(
                    program_id,
                    parent_id,
                    type_arguments,
                    depth,
                )
            }
            _ => None,
        }
    }

    fn get_type_from_intrinsic_alias(
        &self,
        program_id: ProgramId,
        name: &'a str,
        type_arguments: &[Ty<'a>],
        depth: usize,
    ) -> Ty<'a> {
        let Some(type_argument) = type_arguments.first().copied() else {
            return Ty::type_reference(self.arena(), "intrinsic", std::iter::empty());
        };

        match name {
            "Uppercase" | "Lowercase" | "Capitalize" | "Uncapitalize" => {
                self.apply_intrinsic_string_mapping(program_id, name, type_argument, depth + 1)
            }
            "NoInfer" => type_argument,
            "BuiltinIteratorReturn" => Ty::any(),
            _ => Ty::type_reference(self.arena(), "intrinsic", std::iter::empty()),
        }
    }

    fn apply_intrinsic_string_mapping(
        &self,
        program_id: ProgramId,
        name: &'a str,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union.types.iter().map(|ty| {
                    self.apply_intrinsic_string_mapping(program_id, name, *ty, depth + 1)
                }),
            ),
            TypeData::StringLiteral(literal) => Ty::string_literal(
                self.arena(),
                self.apply_intrinsic_string_mapping_to_string(
                    name,
                    literal.value,
                    matches!(name, "Capitalize" | "Uncapitalize"),
                ),
            ),
            TypeData::TemplateLiteral(template) => {
                let mut quasis = template
                    .quasis
                    .iter()
                    .map(|quasi| TemplateLiteralElement { value: quasi.value })
                    .collect::<Vec<_>>();
                let mut expressions = template.expressions.iter().copied().collect::<Vec<_>>();

                match name {
                    "Uppercase" | "Lowercase" => {
                        for quasi in &mut quasis {
                            quasi.value = self.apply_intrinsic_string_mapping_to_string(
                                name,
                                quasi.value,
                                false,
                            );
                        }
                        for expression in &mut expressions {
                            *expression = self.apply_intrinsic_string_mapping(
                                program_id,
                                name,
                                *expression,
                                depth + 1,
                            );
                        }
                    }
                    "Capitalize" | "Uncapitalize" => {
                        if quasis.first().is_some_and(|quasi| quasi.value.is_empty()) {
                            if let Some(expression) = expressions.first_mut() {
                                *expression = self.apply_intrinsic_string_mapping(
                                    program_id,
                                    name,
                                    *expression,
                                    depth + 1,
                                );
                            }
                        } else if let Some(quasi) = quasis.first_mut() {
                            quasi.value = self.apply_intrinsic_string_mapping_to_string(
                                name,
                                quasi.value,
                                true,
                            );
                        }
                    }
                    _ => {}
                }

                self.get_template_literal_type(program_id, quasis, expressions)
            }
            TypeData::TypeReference(reference) if reference.name == name => ty,
            TypeData::TypeReference(_) => {
                let expanded = self.expand_type_at_use(program_id, ty, depth + 1);
                if expanded != ty {
                    self.apply_intrinsic_string_mapping(program_id, name, expanded, depth + 1)
                } else {
                    Ty::type_reference(self.arena(), name, [ty])
                }
            }
            TypeData::String | TypeData::Any | TypeData::Error(_) | TypeData::Unknown => {
                Ty::type_reference(self.arena(), name, [ty])
            }
            _ => ty,
        }
    }

    fn apply_intrinsic_string_mapping_to_string(
        &self,
        name: &str,
        value: &str,
        first_character_only: bool,
    ) -> &'a str {
        let mapped = match name {
            "Uppercase" => {
                if first_character_only {
                    capitalize_first_character(value, true)
                } else {
                    value.to_uppercase()
                }
            }
            "Lowercase" => value.to_lowercase(),
            "Capitalize" => capitalize_first_character(value, true),
            "Uncapitalize" => capitalize_first_character(value, false),
            _ => value.to_string(),
        };
        self.arena().str(&mapped)
    }

    /// Instantiate the pieces of a type-query result that accept explicit type arguments.
    fn instantiate_type_query_type(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        type_arguments: &[Ty<'a>],
    ) -> Ty<'a> {
        match self.arena().type_data(ty) {
            TypeData::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection
                    .types
                    .iter()
                    .map(|ty| self.instantiate_type_query_type(program_id, *ty, type_arguments)),
            ),
            TypeData::Function(function) => {
                self.instantiate_function_type(function, type_arguments)
            }
            TypeData::TypeQuery(query) if query.type_arguments.is_empty() => self
                .instantiate_typeof_class_type(program_id, query, type_arguments)
                .unwrap_or(ty),
            _ => ty,
        }
    }

    /// Partially apply explicit type arguments to a function type.
    fn instantiate_function_type(
        &self,
        function: &TyFunction<'a>,
        type_arguments: &[Ty<'a>],
    ) -> Ty<'a> {
        let mapper = TypeMapper::from_type_parameters_and_arguments(
            self.arena(),
            function.type_parameters.iter().copied(),
            type_arguments.iter().copied(),
        );
        let remaining_type_parameters = function
            .type_parameters
            .iter()
            .skip(type_arguments.len())
            .copied();

        Ty::function_with_type_predicate(
            self.arena(),
            remaining_type_parameters,
            function.parameters.iter().map(|parameter| {
                let ty = self.instantiate_type(parameter.ty, &mapper);
                if parameter.rest {
                    Ty::rest_parameter(parameter.name, ty)
                } else if parameter.optional {
                    Ty::optional_parameter(parameter.name, ty)
                } else {
                    Ty::parameter(parameter.name, ty)
                }
            }),
            self.instantiate_type(function.return_type, &mapper),
            function
                .type_predicate
                .map(|predicate| self.instantiate_type_predicate(*predicate, &mapper)),
        )
    }

    /// Instantiate `typeof Class<T>` into the constructor/prototype shape TypeScript reports.
    fn instantiate_typeof_class_type(
        &self,
        program_id: ProgramId,
        query: &TyTypeQuery<'a>,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        let class_name = query.name;
        let class_symbol = self.get_class_symbol_for_type(program_id, class_name)?;
        let type_parameters = self
            .get_type_parameters_for_type(class_symbol.program_id, class_name)
            .unwrap_or_default();
        let instance_type_arguments = type_parameters
            .iter()
            .enumerate()
            .map(|(index, _)| type_arguments.get(index).copied().unwrap_or_else(Ty::any));
        let prototype_type_arguments = type_parameters.iter().map(|_| Ty::any());

        Some(Ty::object(
            self.arena(),
            [
                Ty::property(
                    "new ()",
                    Ty::type_reference(self.arena(), class_name, instance_type_arguments),
                ),
                Ty::property(
                    "prototype",
                    Ty::type_reference(self.arena(), class_name, prototype_type_arguments),
                ),
            ],
        ))
    }

    fn get_type_from_type_assertion(&self, program_id: ProgramId, ty: &'a TSType<'a>) -> Ty<'a> {
        let ty = match ty {
            TSType::TSTypeReference(reference) => self
                .get_transparent_type_alias_assertion_type(program_id, reference, 0)
                .unwrap_or_else(|| self.get_type_from_ts_type_reference(program_id, reference)),
            _ => self.get_type_from_ts_type(program_id, ty),
        };
        self.with_implicit_type_arguments_visible(ty)
    }

    fn get_transparent_type_alias_assertion_type(
        &self,
        program_id: ProgramId,
        reference: &'a TSTypeReference<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }

        let name = ts_type_name_to_str(self.arena(), &reference.type_name);
        let mut type_arguments = self.type_arguments_from_reference(program_id, reference);

        self.fill_default_type_arguments(program_id, name, &mut type_arguments);

        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, name)?;
        if let Some(ty) = self.get_transparent_type_alias_declaration_assertion_type(
            symbol.program_id,
            declaration,
            &type_arguments,
            depth + 1,
        ) {
            return Some(ty);
        }

        let expanded = self.get_expanded_type_alias_declaration(
            symbol.program_id,
            declaration,
            &type_arguments,
            depth + 1,
        )?;
        expanded
            .is_transparent_type_alias_union_constituent(self.arena())
            .then_some(expanded)
    }

    fn get_transparent_type_alias_declaration_assertion_type(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        type_arguments: &[Ty<'a>],
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }

        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias) => {
                let type_parameter_name =
                    transparent_type_alias_type_parameter_name(&alias.type_annotation)?;
                let type_parameters = self
                    .type_parameters_from_declaration(program_id, alias.type_parameters.as_deref());
                let type_parameter = type_parameters
                    .iter()
                    .find(|type_parameter| type_parameter.name == type_parameter_name)?;
                let substitutions = self.type_parameter_substitutions_for_type_arguments(
                    program_id,
                    alias.type_parameters.as_deref(),
                    type_arguments,
                );
                Some(substitutions.get(*type_parameter).unwrap_or_else(Ty::any))
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_transparent_type_alias_declaration_assertion_type(
                    program_id,
                    parent_id,
                    type_arguments,
                    depth + 1,
                )
            }
            _ => None,
        }
    }

    fn type_alias_declaration_node(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
    ) -> Option<NodeId> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(_) => Some(declaration),
            AstKind::BindingIdentifier(_) => self.type_alias_declaration_node(
                program_id,
                self.nodes(program_id).parent_id(declaration),
            ),
            _ => None,
        }
    }

    pub(crate) fn is_empty_object_intersection_alias_reference(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
    ) -> bool {
        let TypeData::TypeReference(reference) = self.arena().type_data(ty) else {
            return false;
        };
        let Some((symbol, declaration)) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)
        else {
            return false;
        };
        let Some(declaration) = self.type_alias_declaration_node(symbol.program_id, declaration)
        else {
            return false;
        };
        matches!(
            self.nodes(symbol.program_id).kind(declaration),
            AstKind::TSTypeAliasDeclaration(alias)
                if is_empty_object_intersection(&alias.type_annotation)
        )
    }

    fn register_type_alias_metadata(&self, reference_program_id: ProgramId, ty: Ty<'a>) {
        let TypeData::TypeReference(reference) = self.arena().type_data(ty) else {
            return;
        };
        let Some((alias_symbol, declaration)) =
            self.get_type_symbol_and_declaration_for_name(reference_program_id, reference.name)
        else {
            return;
        };
        let Some(declaration) =
            self.type_alias_declaration_node(alias_symbol.program_id, declaration)
        else {
            return;
        };
        self.set_type_alias_metadata(
            ty,
            TypeAliasMetadata {
                reference_program_id,
                alias_symbol,
                declaration: NodeRef::new(alias_symbol.program_id, declaration),
            },
        );
    }

    fn type_reference_with_display_type_argument_count(
        &self,
        program_id: ProgramId,
        name: &'a str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
        display_type_argument_count: usize,
    ) -> Ty<'a> {
        let target = self
            .get_type_symbol_and_declaration_for_name(program_id, name)
            .map(|(symbol, _)| symbol)
            .or_else(|| self.get_enum_member_symbol_for_name(program_id, name));
        let ty = if let Some(target) = target {
            Ty::type_reference_for_symbol(
                self.arena(),
                name,
                target,
                type_arguments,
                display_type_argument_count,
            )
        } else {
            Ty::type_reference_with_display_type_argument_count(
                self.arena(),
                name,
                type_arguments,
                display_type_argument_count,
            )
        };
        self.register_type_alias_metadata(program_id, ty);
        ty
    }

    fn get_type_from_ts_type_reference(
        &self,
        program_id: ProgramId,
        reference: &'a TSTypeReference<'a>,
    ) -> Ty<'a> {
        let name = ts_type_name_to_str(self.arena(), &reference.type_name);
        let mut type_arguments = self.type_arguments_from_reference(program_id, reference);
        let explicit_type_argument_count = type_arguments.len();
        let target = self
            .get_type_symbol_and_declaration_for_name(program_id, name)
            .map(|(symbol, _)| symbol);

        let implicit_display_type_argument_count =
            self.fill_default_type_arguments(program_id, name, &mut type_arguments);
        let should_display_implicit_defaults = !self.hide_implicit_type_argument_display.get()
            && (target
                .and_then(|symbol| self.store.entry(symbol.program_id))
                .is_some_and(program::ProgramEntry::is_lib)
                || (explicit_type_argument_count > 0
                    && implicit_display_type_argument_count > 0
                    && target.is_some_and(|symbol| symbol.program_id == program_id)));

        if let Some(array_type) =
            self.get_global_array_type_reference_type(program_id, name, type_arguments.as_slice())
        {
            return array_type;
        }

        if let Some(alias_type) =
            self.get_expanded_type_query_alias_reference(program_id, name, &type_arguments)
        {
            return alias_type;
        }

        self.type_reference_with_display_type_argument_count(
            program_id,
            name,
            type_arguments.iter().copied(),
            explicit_type_argument_count
                + if should_display_implicit_defaults {
                    implicit_display_type_argument_count
                } else {
                    0
                },
        )
    }

    fn type_arguments_from_reference(
        &self,
        program_id: ProgramId,
        reference: &'a TSTypeReference<'a>,
    ) -> Vec<Ty<'a>> {
        reference
            .type_arguments
            .as_ref()
            .into_iter()
            .flat_map(|args| {
                args.params
                    .iter()
                    .map(|ty| self.get_type_argument_from_ts_type(program_id, ty))
            })
            .collect::<Vec<_>>()
    }

    fn get_type_argument_from_ts_type(&self, program_id: ProgramId, ty: &'a TSType<'a>) -> Ty<'a> {
        let ty = self.get_type_from_ts_type(program_id, ty);
        match self.arena().type_data(ty) {
            TypeData::TypeQuery(query)
                if query.type_arguments.is_empty() && query.resolved.is_error(self.arena()) =>
            {
                query.resolved
            }
            TypeData::TypeQuery(query)
                if query.type_arguments.is_empty() && !query.resolved.is_any() =>
            {
                query.resolved
            }
            _ => self.get_apparent_type_at_use(program_id, ty, 0),
        }
    }

    fn apparent_type_for_conditional_match(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::TypeReference(reference) => self
                .apparent_type_reference_for_conditional_match(program_id, reference, depth + 1)
                .unwrap_or(ty),
            TypeData::Array(array) => {
                let element_type = self.apparent_type_for_conditional_match(
                    program_id,
                    array.element_type,
                    depth + 1,
                );
                if array.readonly {
                    Ty::readonly_array(self.arena(), element_type)
                } else {
                    Ty::array(self.arena(), element_type)
                }
            }
            TypeData::Tuple(tuple) => {
                let elements = tuple
                    .elements
                    .iter()
                    .map(|element| match element {
                        TupleElement::Regular(ty) => TupleElement::Regular(
                            self.apparent_type_for_conditional_match(program_id, *ty, depth + 1),
                        ),
                        TupleElement::Rest(ty) => TupleElement::Rest(
                            self.apparent_type_for_conditional_match(program_id, *ty, depth + 1),
                        ),
                        TupleElement::Optional(ty) => TupleElement::Optional(
                            self.apparent_type_for_conditional_match(program_id, *ty, depth + 1),
                        ),
                    })
                    .collect::<Vec<_>>();
                Ty::tuple_with_labels(
                    self.arena(),
                    elements,
                    tuple.labels.iter().copied().collect(),
                    tuple.readonly,
                )
            }
            TypeData::Union(union) => Ty::r#union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.apparent_type_for_conditional_match(program_id, *ty, depth + 1)),
            ),
            TypeData::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection
                    .types
                    .iter()
                    .map(|ty| self.apparent_type_for_conditional_match(program_id, *ty, depth + 1)),
            ),
            _ => ty,
        }
    }

    fn apparent_type_reference_for_conditional_match(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)?;
        let symbol_has_interface_declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declarations(symbol.symbol_id)
            .any(|declaration| {
                matches!(
                    self.nodes(symbol.program_id).kind(declaration),
                    AstKind::TSInterfaceDeclaration(_)
                ) || matches!(
                    self.nodes(symbol.program_id).parent_kind(declaration),
                    AstKind::TSInterfaceDeclaration(_)
                )
            });
        let symbol_is_from_lib = self
            .store
            .entry(symbol.program_id)
            .is_some_and(program::ProgramEntry::is_lib);
        if (symbol_has_interface_declaration || symbol_is_from_lib)
            && let Some(apparent) =
                self.apparent_interface_type_for_conditional_match(program_id, reference)
        {
            return Some(apparent);
        }
        self.apparent_type_declaration_for_conditional_match(
            symbol.program_id,
            declaration,
            reference,
            depth,
        )
    }

    fn apparent_type_declaration_for_conditional_match(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        reference: &TyTypeReference<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSInterfaceDeclaration(_) => {
                self.apparent_interface_type_for_conditional_match(program_id, reference)
            }
            AstKind::TSTypeAliasDeclaration(alias) => {
                let substitutions = self.type_parameter_substitutions_for_reference(
                    program_id,
                    alias.type_parameters.as_deref(),
                    reference,
                );
                let mapper = substitutions.to_mapper(self.arena());
                let ty = self.instantiate_type(
                    self.get_type_from_ts_type(program_id, &alias.type_annotation),
                    &mapper,
                );
                Some(self.apparent_type_for_conditional_match(program_id, ty, depth + 1))
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.apparent_type_declaration_for_conditional_match(
                    program_id,
                    parent_id,
                    reference,
                    depth + 1,
                )
            }
            _ => None,
        }
    }

    fn apparent_interface_type_for_conditional_match(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> Option<Ty<'a>> {
        let declarations = self.interface_declarations_for_type_name(program_id, reference.name);
        if declarations.is_empty() {
            return None;
        }

        let mut properties = Vec::new();
        let mut signatures = Vec::new();

        for &(program_id, interface) in &declarations {
            let mapper = self.interface_member_mapper(
                program_id,
                interface.type_parameters.as_deref(),
                reference,
            );

            for signature in &interface.body.body {
                match signature {
                    TSSignature::TSPropertySignature(property) => {
                        let Some(name) = property_key_name_str(&property.key) else {
                            continue;
                        };
                        let ty = property.type_annotation.as_deref().map_or_else(
                            Ty::any,
                            |annotation| {
                                self.get_type_from_ts_type(program_id, &annotation.type_annotation)
                            },
                        );
                        let ty = self.instantiate_type(ty, &mapper);
                        properties.push(TyProperty {
                            name,
                            ty,
                            computed: property.computed,
                            optional: property.optional,
                            method: false,
                            readonly: property.readonly,
                        });
                    }
                    TSSignature::TSMethodSignature(method) => {
                        let Some(name) = property_key_name_str(&method.key) else {
                            continue;
                        };
                        if method.kind != TSMethodSignatureKind::Method {
                            if properties
                                .iter()
                                .any(|property: &TyProperty<'_>| property.name == name)
                            {
                                continue;
                            }
                            let Some(ty) = self.get_property_type_of_interface_declarations(
                                reference,
                                name,
                                &declarations,
                            ) else {
                                continue;
                            };
                            let has_setter = declarations.iter().any(|(_, declaration)| {
                                declaration.body.body.iter().any(|signature| {
                                    matches!(
                                        signature,
                                        TSSignature::TSMethodSignature(candidate)
                                            if candidate.kind == TSMethodSignatureKind::Set
                                                && property_key_name_str(&candidate.key) == Some(name)
                                    )
                                })
                            });
                            properties.push(TyProperty {
                                name,
                                ty,
                                computed: method.computed,
                                optional: method.optional,
                                method: false,
                                readonly: !has_setter,
                            });
                            continue;
                        }

                        let signature = self.signature_from_ts_method_signature(program_id, method);
                        let signature = self.instantiate_signature(signature, &mapper);
                        properties.push(TyProperty {
                            name,
                            ty: signature.ty,
                            computed: method.computed,
                            optional: method.optional,
                            method: true,
                            readonly: false,
                        });
                    }
                    _ => {}
                }

                for kind in [SignatureKind::Call, SignatureKind::Construct] {
                    if let Some(signature) =
                        self.signature_from_ts_signature(program_id, signature, kind)
                    {
                        signatures.push(self.instantiate_signature(signature, &mapper));
                    }
                }
            }
        }

        Some(Ty::object_with_signatures(
            self.arena(),
            properties,
            signatures,
        ))
    }

    /// Expand references to aliases whose underlying type is a `typeof` query.
    fn get_expanded_type_query_alias_reference(
        &self,
        program_id: ProgramId,
        type_name: &str,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, type_name)?;
        self.get_expanded_type_query_alias_declaration(
            symbol.program_id,
            declaration,
            type_arguments,
        )
    }

    /// Resolve a type-query alias declaration and substitute the alias type arguments.
    fn get_expanded_type_query_alias_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias)
                if matches!(alias.type_annotation, TSType::TSTypeQuery(_)) =>
            {
                let mapper = TypeMapper::from_type_parameters_and_arguments(
                    self.arena(),
                    self.type_parameters_from_declaration(
                        program_id,
                        alias.type_parameters.as_deref(),
                    ),
                    type_arguments.iter().copied(),
                );
                Some(self.instantiate_type(
                    self.get_type_from_ts_type(program_id, &alias.type_annotation),
                    &mapper,
                ))
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_expanded_type_query_alias_declaration(
                    program_id,
                    parent_id,
                    type_arguments,
                )
            }
            _ => None,
        }
    }

    fn fill_default_type_arguments(
        &self,
        program_id: ProgramId,
        type_name: &str,
        type_arguments: &mut Vec<Ty<'a>>,
    ) -> usize {
        let Some(type_parameters) = self.get_type_parameters_for_type(program_id, type_name) else {
            return 0;
        };
        if type_arguments.len() >= type_parameters.len() {
            return 0;
        }

        let explicit_count = type_arguments.len();
        let mut default_type_arguments = Vec::new();
        let mut substitutions =
            self.explicit_type_argument_substitutions(&type_parameters, type_arguments.as_slice());
        self.add_default_type_argument_substitutions(
            &type_parameters,
            explicit_count,
            &mut substitutions,
            |default_type| default_type_arguments.push(default_type),
        );
        let display_count = if explicit_count == 0 {
            default_type_arguments
                .iter()
                .rposition(|ty| should_display_implicit_default_type_argument(self.arena(), *ty))
                .map_or(0, |index| index + 1)
        } else {
            default_type_arguments
                .iter()
                .rposition(|ty| {
                    matches!(
                        self.arena().type_data(*ty),
                        TypeData::TypeReference(reference)
                            if reference.is_bare() && reference.target.is_none()
                    )
                })
                .map_or(0, |index| index + 1)
        };
        type_arguments.extend(default_type_arguments);
        display_count
    }

    /// Return the instance type for the nearest enclosing class.
    /// This provides a class-backed type for `this` inside methods and field initializers.
    fn get_enclosing_class_instance_type(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
    ) -> Option<Ty<'a>> {
        if let AstKind::Class(class) = self.node_kind(NodeRef::new(program_id, node_id)) {
            return class.id.as_ref().map(|identifier| {
                Ty::type_reference(self.arena(), identifier.name.as_str(), std::iter::empty())
            });
        }

        self.nodes(program_id)
            .ancestors(node_id)
            .find_map(|node| match node.kind() {
                AstKind::Class(class) => class.id.as_ref().map(|identifier| {
                    Ty::type_reference(self.arena(), identifier.name.as_str(), std::iter::empty())
                }),
                _ => None,
            })
    }

    /// Return the base instance type for the nearest enclosing derived class.
    fn get_enclosing_base_class_instance_type(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
    ) -> Option<Ty<'a>> {
        let class = if let AstKind::Class(class) = self.node_kind(NodeRef::new(program_id, node_id))
        {
            Some(class)
        } else {
            self.nodes(program_id)
                .ancestors(node_id)
                .find_map(|node| match node.kind() {
                    AstKind::Class(class) => Some(class),
                    _ => None,
                })
        }?;
        let super_class = class.super_class.as_ref()?;
        let super_type = self.get_type_of_expression_with_node(
            program_id,
            super_class,
            Some(class.node_id.get()),
            GetTypeFlags::NONE,
        );
        let TypeData::TypeQuery(query) = self.arena().type_data(super_type) else {
            return None;
        };
        let type_arguments = class
            .super_type_arguments
            .iter()
            .flat_map(|arguments| arguments.params.iter())
            .map(|argument| self.get_type_from_ts_type(program_id, argument));

        Some(Ty::type_reference(self.arena(), query.name, type_arguments))
    }

    fn get_type_of_object_expression(
        &self,
        program_id: ProgramId,
        object: &'a ObjectExpression<'a>,
        node_id: Option<NodeId>,
        context: ExpressionCheckContext<'a>,
    ) -> Ty<'a> {
        let mut property_flags = context.flags;
        if !context.check_mode.const_context()
            && context
                .contextual_type
                .is_none_or(|ty| !type_contains_literal_type(self.arena(), ty, 0))
        {
            property_flags.remove(GetTypeFlags::PRESERVE_LITERALS);
        }

        let mut explicit_properties: Vec<TyProperty<'a>> = Vec::new();
        let mut spread_properties: Vec<TyProperty<'a>> = Vec::new();
        let mut spread_index_infos: Vec<IndexInfo<'a>> = Vec::new();
        for property in &object.properties {
            match property {
                ObjectPropertyKind::ObjectProperty(property) => {
                    let Some(name) = property_key_name_str(&property.key) else {
                        continue;
                    };
                    let ty = self.get_type_of_expression_with_node(
                        program_id,
                        &property.value,
                        node_id,
                        property_flags,
                    );
                    let property = TyProperty {
                        name,
                        ty,
                        computed: false,
                        optional: false,
                        method: property.method,
                        readonly: context.check_mode.const_context(),
                    };
                    spread_properties.retain(|existing| existing.name != name);
                    if let Some(existing) = explicit_properties
                        .iter_mut()
                        .find(|existing| existing.name == name)
                    {
                        *existing = property;
                    } else {
                        explicit_properties.push(property);
                    }
                }
                ObjectPropertyKind::SpreadProperty(spread) => {
                    let spread_type = self.get_type_of_expression_with_node(
                        program_id,
                        &spread.argument,
                        node_id,
                        property_flags,
                    );
                    let spread_type = self.expand_type_at_use(program_id, spread_type, 0);
                    if spread_type.is_any_like(self.arena()) {
                        return spread_type;
                    }
                    if self.is_invalid_object_spread_type(program_id, spread_type, 0) {
                        return Ty::error(self.arena(), TypeErrorKind::UnsupportedType);
                    }
                    spread_index_infos.extend(
                        spread_type
                            .index_infos(self.arena())
                            .into_iter()
                            .flatten()
                            .copied(),
                    );
                    for spread_property in
                        self.get_object_spread_properties(program_id, spread_type, 0)
                    {
                        let property = TyProperty {
                            readonly: context.check_mode.const_context(),
                            ..spread_property
                        };
                        explicit_properties.retain(|existing| existing.name != property.name);
                        if let Some(existing) = spread_properties
                            .iter_mut()
                            .find(|existing| existing.name == property.name)
                        {
                            *existing = property;
                        } else {
                            spread_properties.push(property);
                        }
                    }
                }
            }
        }

        Ty::object_literal_with_index_infos(
            self.arena(),
            explicit_properties.into_iter().chain(spread_properties),
            spread_index_infos,
        )
    }

    fn is_invalid_object_spread_type(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> bool {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return false;
        }

        let ty = self.expand_type_at_use(program_id, ty, depth + 1);
        match self.arena().type_data(ty) {
            TypeData::Null
            | TypeData::Undefined
            | TypeData::Void
            | TypeData::Never
            | TypeData::Unknown
            | TypeData::Number
            | TypeData::String
            | TypeData::Boolean
            | TypeData::Bigint
            | TypeData::Symbol
            | TypeData::UniqueSymbol(_)
            | TypeData::StringLiteral(_)
            | TypeData::NumberLiteral(_)
            | TypeData::BooleanLiteral(_)
            | TypeData::BigIntLiteral(_)
            | TypeData::TemplateLiteral(_) => true,
            TypeData::Union(union) => union
                .types
                .iter()
                .any(|ty| self.is_invalid_object_spread_type(program_id, *ty, depth + 1)),
            _ => false,
        }
    }

    fn get_object_spread_properties(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Vec<TyProperty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return Vec::new();
        }

        let ty = self.expand_type_at_use(program_id, ty, depth + 1);
        match self.arena().type_data(ty) {
            TypeData::Object(object) => object
                .properties
                .iter()
                .map(|property| TyProperty {
                    method: false,
                    ..*property
                })
                .collect(),
            TypeData::Intersection(intersection) => {
                let mut properties: Vec<TyProperty<'a>> = Vec::new();
                for ty in &intersection.types {
                    for property in self.get_object_spread_properties(program_id, *ty, depth + 1) {
                        if let Some(existing) = properties.iter_mut().find(|existing| {
                            existing.name == property.name && existing.computed == property.computed
                        }) {
                            *existing = property;
                        } else {
                            properties.push(property);
                        }
                    }
                }
                properties
            }
            TypeData::TypeReference(reference) => {
                let mut properties = self.get_object_spread_properties_of_interface(
                    program_id,
                    reference,
                    depth + 1,
                );
                for property in
                    self.get_object_spread_properties_of_class(program_id, reference, depth + 1)
                {
                    if let Some(existing) = properties.iter_mut().find(|existing| {
                        existing.name == property.name && existing.computed == property.computed
                    }) {
                        *existing = property;
                    } else {
                        properties.push(property);
                    }
                }
                properties
            }
            _ => Vec::new(),
        }
    }

    fn get_object_spread_properties_of_interface(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
        depth: usize,
    ) -> Vec<TyProperty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return Vec::new();
        }
        let declarations = self.interface_declarations_for_type_name(program_id, reference.name);
        if declarations.is_empty() {
            return Vec::new();
        }

        let mut properties = Vec::new();
        for computed in [false, true] {
            for &(declaration_program_id, interface) in &declarations {
                for signature in &interface.body.body {
                    let (key, is_computed, optional, method, readonly) = match signature {
                        TSSignature::TSPropertySignature(property) => (
                            &property.key,
                            property.computed,
                            property.optional,
                            false,
                            property.readonly,
                        ),
                        TSSignature::TSMethodSignature(method) => (
                            &method.key,
                            method.computed,
                            method.optional,
                            method.kind == TSMethodSignatureKind::Method,
                            false,
                        ),
                        _ => continue,
                    };
                    let Some(name) = self.resolved_property_key_name(declaration_program_id, key)
                    else {
                        continue;
                    };
                    if is_computed != computed
                        || properties.iter().any(|property: &TyProperty<'_>| {
                            property.name == name && property.computed == computed
                        })
                    {
                        continue;
                    }
                    let Some(ty) = self.get_property_type_of_interface_declarations(
                        reference,
                        name,
                        &declarations,
                    ) else {
                        continue;
                    };
                    properties.push(TyProperty {
                        name,
                        ty,
                        computed,
                        optional,
                        method,
                        readonly,
                    });
                }
            }
        }

        for (heritage_program_id, heritage_type) in
            self.get_interface_heritage_types(program_id, reference)
        {
            for property in
                self.get_object_spread_properties(heritage_program_id, heritage_type, depth + 1)
            {
                if !properties.iter().any(|existing| {
                    existing.name == property.name && existing.computed == property.computed
                }) {
                    properties.push(property);
                }
            }
        }
        properties
    }

    fn get_object_spread_properties_of_class(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
        depth: usize,
    ) -> Vec<TyProperty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return Vec::new();
        }
        let Some(class_symbol) = self.get_class_symbol_for_type(program_id, reference.name) else {
            return Vec::new();
        };
        let Some((class_node_id, class)) = self.get_class_for_symbol(class_symbol) else {
            return Vec::new();
        };
        let substitutions = self.type_parameter_substitutions_for_reference(
            class_symbol.program_id,
            class.type_parameters.as_deref(),
            reference,
        );
        let mapper = substitutions.to_mapper(self.arena());

        let mut properties = Vec::new();
        for computed in [false, true] {
            for element in &class.body.body {
                let ClassElement::PropertyDefinition(property) = element else {
                    continue;
                };
                if property.r#static || property.computed != computed {
                    continue;
                }
                let Some(name) =
                    self.resolved_property_key_name(class_symbol.program_id, &property.key)
                else {
                    continue;
                };
                properties.push(TyProperty {
                    name,
                    ty: self.instantiate_type(
                        self.get_type_of_property_definition(
                            class_symbol.program_id,
                            property,
                            Some(class_node_id),
                        ),
                        &mapper,
                    ),
                    computed,
                    optional: property.optional,
                    method: false,
                    readonly: property.readonly,
                });
            }
        }
        properties
    }

    fn interface_declarations_for_type_name(
        &self,
        program_id: ProgramId,
        type_name: &str,
    ) -> Vec<(ProgramId, &'a TSInterfaceDeclaration<'a>)> {
        let Some((symbol, _)) =
            self.get_type_symbol_and_declaration_for_name(program_id, type_name)
        else {
            return Vec::new();
        };
        let Some(symbol_program) = self.store.entry(symbol.program_id) else {
            return Vec::new();
        };
        if !symbol_program.is_lib() && symbol_program.module_record().has_module_syntax {
            self.interface_declarations_for_symbol(symbol)
                .into_iter()
                .map(|interface| (symbol.program_id, interface))
                .collect()
        } else {
            self.interface_declarations_for_name(type_name)
                .iter()
                .copied()
                .filter(|(program_id, _)| {
                    self.store.entry(*program_id).is_some_and(|entry| {
                        entry.is_lib() || !entry.module_record().has_module_syntax
                    })
                })
                .collect()
        }
    }

    fn get_type_of_static_member_expression(
        &self,
        program_id: ProgramId,
        member: &'a StaticMemberExpression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        let object_type =
            self.get_type_of_expression_with_node(program_id, &member.object, node_id, flags);
        let property_name = member.property.name.as_str();
        let in_chain = self.is_in_chain_expression(program_id, node_id);
        let ty = match self.arena().type_data(object_type) {
            TypeData::Intersection(intersection) => {
                let property_types = intersection
                    .types
                    .iter()
                    .filter_map(|ty| {
                        self.get_property_type_of_static_member_type(program_id, *ty, property_name)
                    })
                    .collect::<Vec<_>>();
                (!property_types.is_empty()).then(|| Ty::intersection(self.arena(), property_types))
            }
            _ => {
                self.get_property_type_of_static_member_type(program_id, object_type, property_name)
            }
        }
        .or_else(|| {
            if matches!(member.object, Expression::ThisExpression(_)) {
                node_id
                    .and_then(|node_id| self.get_enclosing_class_instance_type(program_id, node_id))
                    .and_then(|this_type| {
                        self.get_property_type_of_named_type(program_id, &this_type, property_name)
                    })
            } else {
                None
            }
        })
        .unwrap_or_else(|| {
            if object_type.is_any_like(self.arena()) {
                object_type
            } else {
                Ty::error(self.arena(), TypeErrorKind::UnresolvedMember)
            }
        });
        let ty = if ty.is_function(self.arena()) {
            ty
        } else {
            self.get_apparent_type_at_use(program_id, ty, 0)
        };
        let ty = flow::get_flow_type_of_static_member_reference(self, program_id, member, ty);
        if in_chain {
            ty.or_undefined(self.arena())
        } else {
            ty
        }
    }

    fn get_property_type_of_static_member_type(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let apparent_object_type = self.get_apparent_type_at_use(program_id, object_type, 0);
        self.get_property_type_of_structural_type(program_id, object_type, property_name)
            .or_else(|| {
                self.get_property_type_of_structural_type(
                    program_id,
                    apparent_object_type,
                    property_name,
                )
            })
            .or_else(|| {
                self.get_property_type_of_global_interface_type(
                    program_id,
                    object_type,
                    property_name,
                )
            })
            .or_else(|| {
                self.get_property_type_of_named_type(program_id, &object_type, property_name)
            })
    }

    fn get_type_of_private_field_expression(
        &self,
        program_id: ProgramId,
        member: &'a PrivateFieldExpression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        let object_type =
            self.get_type_of_expression_with_node(program_id, &member.object, node_id, flags);
        let (class_name, is_static) = match self.arena().type_data(object_type) {
            TypeData::TypeReference(reference) => (reference.name, false),
            TypeData::TypeQuery(query) => (query.name, true),
            TypeData::Any => return Ty::any(),
            TypeData::Error(_) => return object_type,
            _ => return Ty::error(self.arena(), TypeErrorKind::UnsupportedType),
        };
        let Some(class_symbol) = self.get_class_symbol_for_type(program_id, class_name) else {
            return Ty::error(self.arena(), TypeErrorKind::UnresolvedType);
        };
        let Some((class_node_id, class)) = self.get_class_for_symbol(class_symbol) else {
            return Ty::error(self.arena(), TypeErrorKind::UnresolvedType);
        };
        let private_name = member.field.name.as_str();
        let ty = class.body.body.iter().find_map(|element| match element {
            ClassElement::MethodDefinition(method)
                if method.r#static == is_static
                    && matches!(
                        &method.key,
                        oxc_ast::ast::PropertyKey::PrivateIdentifier(identifier)
                            if identifier.name == private_name
                    ) =>
            {
                Some(self.get_type_of_method_definition(
                    class_symbol.program_id,
                    method,
                    class_node_id,
                ))
            }
            ClassElement::PropertyDefinition(property)
                if property.r#static == is_static
                    && matches!(
                        &property.key,
                        oxc_ast::ast::PropertyKey::PrivateIdentifier(identifier)
                            if identifier.name == private_name
                    ) =>
            {
                Some(self.get_type_of_property_definition(
                    class_symbol.program_id,
                    property,
                    Some(class_node_id),
                ))
            }
            _ => None,
        });
        let ty = ty.unwrap_or_else(|| Ty::error(self.arena(), TypeErrorKind::UnresolvedMember));
        if member.optional {
            ty.or_undefined(self.arena())
        } else {
            ty
        }
    }

    // TODO: Refactor this into a more general function like `get_property_of_type`
    fn get_property_type_of_structural_type(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        match self.arena().type_data(ty) {
            TypeData::Union(union) => {
                // TODO(correctness): check if there are cases we don't want to do this.
                // By default, if we are accessing a property on a type that might be null or undefined,
                // we want to ignore the null and undefined types.
                let property_types = union
                    .types
                    .iter()
                    .filter_map(|ty| {
                        let ty = self.remove_null_or_undefined(*ty);
                        if ty.is_never() {
                            None
                        } else {
                            self.get_property_type_of_structural_type(program_id, ty, property_name)
                        }
                    })
                    .collect::<Vec<_>>();
                (!property_types.is_empty()).then(|| Ty::union(self.arena(), property_types))
            }
            TypeData::TypeReference(_) => {
                // Resolve type reference into its underlying type
                let resolved_type = self.expand_type_at_use(program_id, ty, 0);
                if matches!(
                    self.arena().type_data(resolved_type),
                    TypeData::TypeReference(_)
                ) {
                    return None;
                }
                self.get_property_type_of_structural_type(program_id, resolved_type, property_name)
            }
            TypeData::TypeQuery(query) => {
                self.get_property_type_of_structural_type(program_id, query.resolved, property_name)
            }
            TypeData::Intersection(intersection) => intersection.types.iter().find_map(|ty| {
                self.get_property_type_of_structural_type(program_id, *ty, property_name)
            }),
            TypeData::Tuple(tuple) => self.get_property_type_of_tuple(ty, tuple, property_name),
            TypeData::Object(object) => {
                if let Some(property) = object
                    .properties
                    .iter()
                    .find(|property| property.name == property_name && !property.computed)
                {
                    return Some(if property.optional {
                        Ty::union(self.arena(), [property.ty, Ty::Undefined])
                    } else {
                        property.ty
                    });
                }

                // Try to get an index signature from the resolved type
                for index_info in &object.index_infos {
                    // TODO(correctness): Don't hard-code the key type here
                    if index_info.key_type == Ty::string() {
                        return Some(index_info.value_type);
                    }
                }
                None
            }
            TypeData::ModuleNamespace(namespace) => {
                namespace.properties.iter().find_map(|property| {
                    // TODO(correctness): handle all readonly/optional cases
                    (property.name == property_name && !property.computed).then_some(
                        if property.optional {
                            Ty::union(self.arena(), [property.ty, Ty::Undefined])
                        } else {
                            property.ty
                        },
                    )
                })
            }
            TypeData::Mapped(map) => match self.arena().type_data(map.constraint) {
                TypeData::StringLiteral(string_lit) => {
                    if string_lit.value == property_name {
                        Some(map.template)
                    } else {
                        None
                    }
                }
                // TODO(completeness): handle more cases
                _ => None,
            },
            // TODO(completeness): handle all types explicitly
            _ => None,
        }
    }

    fn get_property_type_of_tuple(
        &self,
        tuple_type: Ty<'a>,
        tuple: &crate::types::TyTuple<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        if property_name == "length" {
            if tuple
                .elements
                .iter()
                .any(|element| matches!(element, TupleElement::Rest(_)))
            {
                return Some(Ty::number());
            }

            let minimum_length = tuple
                .elements
                .iter()
                .filter(|element| matches!(element, TupleElement::Regular(_)))
                .count();
            return Some(Ty::union(
                self.arena(),
                (minimum_length..=tuple.elements.len()).map(|length| {
                    let raw = self.arena().str(&length.to_string());
                    Ty::number_literal(self.arena(), length as f64, raw, NumberBase::Decimal)
                }),
            ));
        }

        let index = property_name.parse::<usize>().ok()?;
        (index.to_string() == property_name)
            .then(|| tuple_element_type_at_index(self.arena(), tuple_type, index))
            .flatten()
    }

    fn get_type_of_computed_member_expression(
        &self,
        program_id: ProgramId,
        member: &'a ComputedMemberExpression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        let object_type =
            self.get_type_of_expression_with_node(program_id, &member.object, node_id, flags);
        let object_type = self.remove_null_or_undefined(object_type);
        let key_type = self.get_type_of_expression_with_node(
            program_id,
            &member.expression,
            node_id,
            flags | GetTypeFlags::PRESERVE_LITERALS,
        );
        let lookup_key_type = self.expand_type_for_index_lookup(program_id, key_type, 0);
        let indexed_access_resolution =
            self.resolve_indexed_access_type(program_id, node_id, object_type, lookup_key_type);
        if let IndexedAccessResolution::Resolved(indexed_type) = indexed_access_resolution {
            return indexed_type;
        }

        // Try accessing like tuple with specific numeric key
        if key_type.is_number_like(self.arena())
            && let Some(index) = tuple_index_from_expression(&member.expression)
            && let Some(element_type) =
                tuple_element_type_at_index(self.arena(), object_type, index)
        {
            return element_type;
        };

        // Try accessing as array with a generic numeric key
        if key_type.is_number_like(self.arena())
            && let Some(element_type) = self
                .remove_null_or_undefined(object_type)
                .array_element_type(self.arena())
        {
            return element_type;
        }

        // Try accessing as an object with an index signature
        let object_type = self.remove_null_or_undefined(object_type);
        let (object_program_id, object_type) = self
            .get_expanded_type_alias_reference_preserving_arguments(program_id, object_type, 0)
            .unwrap_or((program_id, object_type));
        let object_type = self.expand_type_at_use(object_program_id, object_type, 0);
        if let TypeData::Object(object) = self.arena().type_data(object_type)
            && let Some(index_info) = object
                .index_infos
                .iter()
                .find(|index_info| self.is_assignable_to(lookup_key_type, index_info.key_type))
        {
            return index_info.value_type;
        }

        if matches!(indexed_access_resolution, IndexedAccessResolution::Deferred) {
            return Ty::indexed_access(self.arena(), object_type, key_type);
        }

        if object_type.is_error(self.arena()) {
            object_type
        } else if key_type.is_error(self.arena()) {
            key_type
        } else if object_type.is_any() {
            object_type
        } else if key_type.is_any() {
            key_type
        } else {
            Ty::error(self.arena(), TypeErrorKind::UnresolvedMember)
        }
    }

    fn get_property_type_of_global_interface_type(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let interface_type = match self.arena().type_data(object_type) {
            TypeData::Union(union) => {
                let property_types = union
                    .types
                    .iter()
                    .filter_map(|ty| {
                        let ty = self.remove_null_or_undefined(*ty);
                        (!ty.is_never()).then_some(ty)
                    })
                    .map(|ty| {
                        self.get_property_type_of_global_interface_type(
                            program_id,
                            ty,
                            property_name,
                        )
                    })
                    .collect::<Option<Vec<_>>>();
                return property_types.and_then(|property_types| {
                    (!property_types.is_empty()).then(|| Ty::union(self.arena(), property_types))
                });
            }
            TypeData::Intersection(intersection) => {
                let property_types = intersection
                    .types
                    .iter()
                    .filter_map(|ty| {
                        self.get_property_type_of_global_interface_type(
                            program_id,
                            *ty,
                            property_name,
                        )
                    })
                    .collect::<Vec<_>>();
                return (!property_types.is_empty())
                    .then(|| Ty::intersection(self.arena(), property_types));
            }
            TypeData::GlobalThis => {
                if property_name == GLOBAL_THIS_IDENT.as_str() {
                    return Some(Ty::global_this());
                }
                return self
                    .global_symbols
                    .global_this_value_symbol(property_name)
                    .map(|symbol| self.get_type_of_symbol(symbol));
            }
            TypeData::Array(array) if array.readonly => {
                Some(self.get_global_readonly_array_type(program_id, array.element_type))
            }
            TypeData::Array(array) => {
                Some(self.get_global_array_type(program_id, array.element_type))
            }
            TypeData::Tuple(tuple) => {
                let element_type = Ty::union(
                    self.arena(),
                    tuple.elements.iter().map(|element| match element {
                        TupleElement::Regular(ty) | TupleElement::Optional(ty) => *ty,
                        TupleElement::Rest(ty) => {
                            ty.array_element_type(self.arena()).unwrap_or(*ty)
                        }
                    }),
                );
                if tuple.readonly {
                    Some(self.get_global_readonly_array_type(program_id, element_type))
                } else {
                    Some(self.get_global_array_type(program_id, element_type))
                }
            }
            TypeData::Object(object) => {
                return self.get_property_type_of_global_function_augmented_object_type(
                    program_id,
                    object,
                    property_name,
                );
            }
            TypeData::PrimitiveObject => Some(self.get_global_object_type(program_id)),
            TypeData::Function(_) => {
                return self.get_property_type_of_global_function_augmented_type(
                    program_id,
                    true,
                    false,
                    property_name,
                );
            }
            TypeData::String | TypeData::StringLiteral(_) => {
                Some(self.get_global_string_type(program_id))
            }
            TypeData::Boolean | TypeData::BooleanLiteral(_) => {
                Some(self.get_global_boolean_type(program_id))
            }
            TypeData::Number | TypeData::NumberLiteral(_) => {
                Some(self.get_global_number_type(program_id))
            }
            TypeData::Symbol | TypeData::UniqueSymbol(_) => {
                Some(self.get_global_symbol_type(program_id))
            }
            TypeData::Bigint | TypeData::BigIntLiteral(_) => {
                Some(self.get_global_bigint_type(program_id))
            }
            TypeData::TypeReference(_) => {
                let expanded = self.expand_type_at_use(program_id, object_type, 0);
                if expanded != object_type {
                    return self.get_property_type_of_global_interface_type(
                        program_id,
                        expanded,
                        property_name,
                    );
                }

                let has_call_signatures = !self
                    .get_signatures_of_type_in_program(program_id, object_type, SignatureKind::Call)
                    .is_empty();
                let has_construct_signatures = !has_call_signatures
                    && !self
                        .get_signatures_of_type_in_program(
                            program_id,
                            object_type,
                            SignatureKind::Construct,
                        )
                        .is_empty();
                return self.get_property_type_of_global_function_augmented_type(
                    program_id,
                    has_call_signatures,
                    has_construct_signatures,
                    property_name,
                );
            }
            _ => return None,
        };
        self.get_property_type_of_global_interface_reference(
            program_id,
            interface_type?,
            property_name,
        )
    }

    fn get_property_type_of_global_function_augmented_object_type(
        &self,
        program_id: ProgramId,
        object: &TyObject<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        self.get_property_type_of_global_function_augmented_type(
            program_id,
            object
                .signatures
                .iter()
                .any(|signature| signature.kind == SignatureKind::Call),
            object
                .signatures
                .iter()
                .any(|signature| signature.kind == SignatureKind::Construct),
            property_name,
        )
    }

    fn get_property_type_of_global_function_augmented_type(
        &self,
        program_id: ProgramId,
        has_call_signatures: bool,
        has_construct_signatures: bool,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let function_type = if has_call_signatures {
            Some(self.get_global_callable_function_type(program_id))
        } else if has_construct_signatures {
            Some(self.get_global_newable_function_type(program_id))
        } else {
            None
        };

        function_type
            .and_then(|ty| {
                self.get_property_type_of_global_interface_reference(program_id, ty, property_name)
            })
            .or_else(|| {
                if has_call_signatures || has_construct_signatures {
                    let function_type = self.get_global_function_type(program_id);
                    self.get_property_type_of_global_interface_reference(
                        program_id,
                        function_type,
                        property_name,
                    )
                } else {
                    None
                }
            })
            .or_else(|| {
                let object_type = self.get_global_object_type(program_id);
                self.get_property_type_of_global_interface_reference(
                    program_id,
                    object_type,
                    property_name,
                )
            })
    }

    fn get_property_type_of_global_interface_reference(
        &self,
        program_id: ProgramId,
        interface_type: Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let TypeData::TypeReference(reference) = self.arena().type_data(interface_type) else {
            return None;
        };
        self.get_property_type_of_interface_type(program_id, reference, property_name)
    }

    fn is_in_contextually_typed_initializer(&self, program_id: ProgramId, node_id: NodeId) -> bool {
        self.nodes(program_id)
            .ancestors(node_id)
            .any(|node| match node.kind() {
                AstKind::VariableDeclarator(declarator) => declarator.type_annotation.is_some(),
                AstKind::PropertyDefinition(property) => property.type_annotation.is_some(),
                _ => false,
            })
    }

    fn is_in_const_context(&self, program_id: ProgramId, node_id: NodeId) -> bool {
        for ancestor in self.nodes(program_id).ancestors(node_id) {
            match ancestor.kind() {
                AstKind::TSAsExpression(assertion) => {
                    return is_const_type_reference(&assertion.type_annotation);
                }
                AstKind::ObjectProperty(_)
                | AstKind::ObjectExpression(_)
                | AstKind::ArrayExpression(_)
                | AstKind::ParenthesizedExpression(_)
                | AstKind::SpreadElement(_) => {}
                _ => return false,
            }
        }
        false
    }

    fn get_type_of_call_expression(
        &self,
        program_id: ProgramId,
        call_expression: &'a CallExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let callee_type = self.get_type_of_expression_with_node(
            program_id,
            &call_expression.callee,
            node_id,
            GetTypeFlags::NONE,
        );
        let candidates =
            self.get_signatures_of_type_in_program(program_id, callee_type, SignatureKind::Call);
        if candidates.is_empty() {
            return if callee_type.is_any_like(self.arena()) {
                callee_type
            } else {
                Ty::error(self.arena(), TypeErrorKind::UnsupportedType)
            };
        }

        let applicable = candidates
            .iter()
            .filter_map(|signature| {
                self.resolve_call_signature_candidate(
                    program_id,
                    *signature,
                    call_expression,
                    node_id,
                    true,
                )
            })
            .collect::<Vec<_>>();

        self.choose_best_signature_candidate(applicable)
            .or_else(|| {
                // TODO(overloads): mirror TypeScript Go's overload failure candidate diagnostics
                // instead of falling back to the first signature return type.
                candidates.first().and_then(|signature| {
                    self.resolve_call_signature_candidate(
                        program_id,
                        *signature,
                        call_expression,
                        node_id,
                        false,
                    )
                })
            })
            .map(ResolvedSignatureCandidate::into_return_type)
            .unwrap_or_else(|| {
                if callee_type.is_any_like(self.arena()) {
                    callee_type
                } else {
                    Ty::error(self.arena(), TypeErrorKind::UnsupportedType)
                }
            })
    }

    fn get_type_of_tagged_template_expression(
        &self,
        program_id: ProgramId,
        tagged_template: &'a TaggedTemplateExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let tag_type = self.get_type_of_expression_with_node(
            program_id,
            &tagged_template.tag,
            node_id,
            GetTypeFlags::NONE,
        );
        let candidates =
            self.get_signatures_of_type_in_program(program_id, tag_type, SignatureKind::Call);
        if candidates.is_empty() {
            return if tag_type.is_any_like(self.arena()) {
                tag_type
            } else {
                Ty::error(self.arena(), TypeErrorKind::UnsupportedType)
            };
        }

        let applicable = candidates
            .iter()
            .filter_map(|signature| {
                self.resolve_tagged_template_signature_candidate(
                    program_id,
                    *signature,
                    tagged_template,
                    node_id,
                    true,
                )
            })
            .collect::<Vec<_>>();

        self.choose_best_signature_candidate(applicable)
            .or_else(|| {
                candidates.first().and_then(|signature| {
                    self.resolve_tagged_template_signature_candidate(
                        program_id,
                        *signature,
                        tagged_template,
                        node_id,
                        false,
                    )
                })
            })
            .map(ResolvedSignatureCandidate::into_return_type)
            .unwrap_or_else(|| {
                if tag_type.is_any_like(self.arena()) {
                    tag_type
                } else {
                    Ty::error(self.arena(), TypeErrorKind::UnsupportedType)
                }
            })
    }

    fn resolve_tagged_template_signature_candidate(
        &self,
        program_id: ProgramId,
        signature: Signature<'a>,
        tagged_template: &'a TaggedTemplateExpression<'a>,
        node_id: Option<NodeId>,
        require_applicable: bool,
    ) -> Option<ResolvedSignatureCandidate<'a>> {
        let function = signature.function(self.arena());
        let argument_types =
            self.get_tagged_template_argument_types(program_id, function, tagged_template, node_id);
        let inference = self.infer_call_type_parameter_resolution_from_argument_types(
            program_id,
            function,
            tagged_template.type_arguments.as_deref(),
            argument_types.iter().copied(),
        );

        if require_applicable
            && !self.is_tagged_template_signature_applicable(
                program_id,
                function,
                tagged_template,
                node_id,
                inference.substitutions(),
            )
        {
            return None;
        }

        let return_type = self.instantiate_signature_return_type(
            program_id,
            function.return_type,
            inference.mapper(),
        );
        Some(ResolvedSignatureCandidate {
            signature,
            inference,
            return_type,
        })
    }

    fn get_tagged_template_argument_types(
        &self,
        program_id: ProgramId,
        function: &TyFunction<'a>,
        tagged_template: &'a TaggedTemplateExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Vec<(usize, Ty<'a>)> {
        let mut argument_types = vec![(0, Ty::any())];
        argument_types.extend(tagged_template.quasi.expressions.iter().enumerate().map(
            |(index, expression)| {
                let argument_index = index + 1;
                let parameter_type = self.get_call_parameter_type_at(function, argument_index);
                let flags =
                    if parameter_type.is_some_and(|ty| self.could_contain_type_variables(ty)) {
                        GetTypeFlags::PRESERVE_LITERALS
                    } else {
                        GetTypeFlags::NONE
                    };
                let argument_type =
                    self.get_type_of_expression_with_node(program_id, expression, node_id, flags);
                (argument_index, argument_type)
            },
        ));
        argument_types
    }

    fn is_tagged_template_signature_applicable(
        &self,
        program_id: ProgramId,
        function: &TyFunction<'a>,
        tagged_template: &'a TaggedTemplateExpression<'a>,
        node_id: Option<NodeId>,
        substitutions: &TypeParameterSubstitutions<'a>,
    ) -> bool {
        let type_argument_count = tagged_template
            .type_arguments
            .as_ref()
            .map_or(0, |type_arguments| type_arguments.params.len());
        if type_argument_count > function.type_parameters.len() {
            return false;
        }

        let argument_count = tagged_template.quasi.expressions.len() + 1;
        let minimum_argument_count = function_minimum_argument_count(self.arena(), function);
        let maximum_argument_count = function_maximum_argument_count(self.arena(), function);
        if argument_count < minimum_argument_count
            || maximum_argument_count.is_some_and(|maximum| argument_count > maximum)
        {
            return false;
        }

        self.arguments_are_assignable_to_parameters(
            program_id,
            function,
            std::iter::once(None).chain(tagged_template.quasi.expressions.iter().map(Some)),
            node_id,
            substitutions,
        )
    }

    fn choose_best_signature_candidate(
        &self,
        mut candidates: Vec<ResolvedSignatureCandidate<'a>>,
    ) -> Option<ResolvedSignatureCandidate<'a>> {
        if candidates.is_empty() {
            return None;
        }

        let mut best_index = 0;
        for index in 1..candidates.len() {
            if self
                .signature_candidate_is_more_specific(&candidates[index], &candidates[best_index])
            {
                best_index = index;
            }
        }

        Some(candidates.swap_remove(best_index))
    }

    fn signature_candidate_is_more_specific(
        &self,
        left: &ResolvedSignatureCandidate<'a>,
        right: &ResolvedSignatureCandidate<'a>,
    ) -> bool {
        let left_function = left.signature.function(self.arena());
        let right_function = right.signature.function(self.arena());
        let parameter_count = left_function
            .parameters
            .len()
            .min(right_function.parameters.len());
        let mut left_better = false;
        let mut right_better = false;

        for index in 0..parameter_count {
            let Some(left_type) = self.candidate_parameter_type_at(left, index) else {
                continue;
            };
            let Some(right_type) = self.candidate_parameter_type_at(right, index) else {
                continue;
            };
            if left_type == right_type {
                continue;
            }
            if self.is_empty_object_type(left_type) && !self.is_empty_object_type(right_type) {
                if self.candidate_has_complete_inference(right) {
                    right_better = true;
                    continue;
                }
            } else if self.is_empty_object_type(right_type)
                && !self.is_empty_object_type(left_type)
                && self.candidate_has_complete_inference(left)
            {
                left_better = true;
                continue;
            }
            let left_assignable = self.is_assignable_to(left_type, right_type);
            let right_assignable = self.is_assignable_to(right_type, left_type);
            if left_assignable && right_assignable {
                left_better |=
                    self.is_empty_object_type(right_type) && !self.is_empty_object_type(left_type);
                right_better |=
                    self.is_empty_object_type(left_type) && !self.is_empty_object_type(right_type);
            } else {
                left_better |= left_assignable;
                right_better |= right_assignable;
            }
        }

        left_better && !right_better
    }

    fn is_empty_object_type(&self, ty: Ty<'a>) -> bool {
        matches!(self.arena().type_data(ty), TypeData::PrimitiveObject)
            || matches!(self.arena().type_data(ty), TypeData::Object(object) if object.is_empty())
    }

    fn candidate_has_complete_inference(&self, candidate: &ResolvedSignatureCandidate<'a>) -> bool {
        candidate
            .signature
            .function(self.arena())
            .type_parameters
            .iter()
            .all(|parameter| {
                candidate
                    .inference
                    .substitutions()
                    .get(*parameter)
                    .is_some()
            })
    }

    fn candidate_parameter_type_at(
        &self,
        candidate: &ResolvedSignatureCandidate<'a>,
        index: usize,
    ) -> Option<Ty<'a>> {
        self.get_call_parameter_type_at(candidate.signature.function(self.arena()), index)
            .map(|ty| self.instantiate_type(ty, candidate.inference.mapper()))
    }

    fn get_signatures_of_type_in_program(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        kind: SignatureKind,
    ) -> Vec<Signature<'a>> {
        let signatures = self.get_signatures_of_type(ty, kind);
        if !signatures.is_empty() {
            return signatures;
        }

        let TypeData::TypeReference(reference) = self.arena().type_data(ty) else {
            return signatures;
        };
        self.get_signatures_of_type_reference(program_id, reference, kind)
    }

    fn get_signatures_of_type_reference(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
        kind: SignatureKind,
    ) -> Vec<Signature<'a>> {
        let interface_signatures = self
            .interface_declarations_for_type_name(program_id, reference.name)
            .into_iter()
            .flat_map(|(program_id, interface)| {
                self.get_signatures_of_interface_declaration(program_id, interface, reference, kind)
            })
            .collect::<Vec<_>>();
        if !interface_signatures.is_empty() {
            return interface_signatures;
        }

        let Some((symbol, declaration)) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)
        else {
            return Vec::new();
        };
        self.get_signatures_of_type_declaration(symbol.program_id, declaration, reference, kind)
    }

    fn get_signatures_of_interface_declaration(
        &self,
        program_id: ProgramId,
        interface: &'a TSInterfaceDeclaration<'a>,
        reference: &TyTypeReference<'a>,
        kind: SignatureKind,
    ) -> Vec<Signature<'a>> {
        let substitutions = self.type_parameter_substitutions_for_reference(
            program_id,
            interface.type_parameters.as_deref(),
            reference,
        );
        let mapper = substitutions.to_mapper(self.arena());
        interface
            .body
            .body
            .iter()
            .filter_map(|signature| self.signature_from_ts_signature(program_id, signature, kind))
            .map(|signature| self.instantiate_signature(signature, &mapper))
            .collect()
    }

    fn get_signatures_of_type_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        reference: &TyTypeReference<'a>,
        kind: SignatureKind,
    ) -> Vec<Signature<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSInterfaceDeclaration(interface) => {
                self.get_signatures_of_interface_declaration(program_id, interface, reference, kind)
            }
            AstKind::TSTypeAliasDeclaration(alias) => {
                let mapper = self
                    .type_parameter_substitutions_for_reference(
                        program_id,
                        alias.type_parameters.as_deref(),
                        reference,
                    )
                    .to_mapper(self.arena());
                self.get_signatures_of_type(
                    self.instantiate_type(
                        self.get_type_from_ts_type(program_id, &alias.type_annotation),
                        &mapper,
                    ),
                    kind,
                )
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_signatures_of_type_declaration(program_id, parent_id, reference, kind)
            }
            _ => Vec::new(),
        }
    }

    fn signature_from_ts_signature(
        &self,
        program_id: ProgramId,
        signature: &'a TSSignature<'a>,
        expected_kind: SignatureKind,
    ) -> Option<Signature<'a>> {
        let signature = match signature {
            TSSignature::TSCallSignatureDeclaration(signature)
                if expected_kind == SignatureKind::Call =>
            {
                self.signature_from_function_parts_with_this(
                    program_id,
                    SignatureKind::Call,
                    signature.type_parameters.as_deref(),
                    signature.this_param.as_deref(),
                    signature.params.as_ref(),
                    signature.return_type.as_deref(),
                )
            }
            TSSignature::TSConstructSignatureDeclaration(signature)
                if expected_kind == SignatureKind::Construct =>
            {
                self.signature_from_function_parts(
                    program_id,
                    SignatureKind::Construct,
                    signature.type_parameters.as_deref(),
                    signature.params.as_ref(),
                    signature.return_type.as_deref(),
                )
            }
            _ => return None,
        };
        Some(signature)
    }

    fn signature_from_type_literal_signature(
        &self,
        program_id: ProgramId,
        signature: &'a TSSignature<'a>,
    ) -> Option<Signature<'a>> {
        let (kind, type_parameters, this_param, parameters, return_type) = match signature {
            TSSignature::TSCallSignatureDeclaration(signature) => (
                SignatureKind::Call,
                signature.type_parameters.as_deref(),
                signature.this_param.as_deref(),
                signature.params.as_ref(),
                signature.return_type.as_deref(),
            ),
            TSSignature::TSConstructSignatureDeclaration(signature) => (
                SignatureKind::Construct,
                signature.type_parameters.as_deref(),
                None,
                signature.params.as_ref(),
                signature.return_type.as_deref(),
            ),
            _ => return None,
        };

        Some(self.signature_from_function_parts_with_this(
            program_id,
            kind,
            type_parameters,
            this_param,
            parameters,
            return_type,
        ))
    }

    fn signature_from_ts_method_signature(
        &self,
        program_id: ProgramId,
        method: &'a TSMethodSignature<'a>,
    ) -> Signature<'a> {
        self.signature_from_function_parts_with_this(
            program_id,
            SignatureKind::Call,
            method.type_parameters.as_deref(),
            method.this_param.as_deref(),
            method.params.as_ref(),
            method.return_type.as_deref(),
        )
    }

    fn signature_from_function_parts(
        &self,
        program_id: ProgramId,
        kind: SignatureKind,
        type_parameters: Option<&'a oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        parameters: &'a FormalParameters<'a>,
        return_type: Option<&'a TSTypeAnnotation<'a>>,
    ) -> Signature<'a> {
        self.signature_from_function_parts_with_this(
            program_id,
            kind,
            type_parameters,
            None,
            parameters,
            return_type,
        )
    }

    fn signature_from_function_parts_with_this(
        &self,
        program_id: ProgramId,
        kind: SignatureKind,
        type_parameters: Option<&'a oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        this_param: Option<&'a TSThisParameter<'a>>,
        parameters: &'a FormalParameters<'a>,
        return_type: Option<&'a TSTypeAnnotation<'a>>,
    ) -> Signature<'a> {
        let previous_hide_implicit_type_argument_display =
            self.hide_implicit_type_argument_display.replace(true);
        let parameters = self.function_type_parameters(program_id, this_param, parameters);
        let (return_type, type_predicate) = self.return_type_and_type_predicate_from_annotation(
            program_id,
            &parameters,
            return_type,
        );
        self.hide_implicit_type_argument_display
            .set(previous_hide_implicit_type_argument_display);
        let ty = Ty::function_with_type_predicate(
            self.arena(),
            self.type_parameters_from_declaration(program_id, type_parameters),
            parameters,
            return_type,
            type_predicate,
        );
        let TypeData::Function(_) = self.arena().type_data(ty) else {
            unreachable!("signature construction always creates a function type")
        };
        Signature::new(kind, ty)
    }

    fn return_type_and_type_predicate_from_annotation(
        &self,
        program_id: ProgramId,
        parameters: &[TyParameter<'a>],
        return_type: Option<&'a TSTypeAnnotation<'a>>,
    ) -> (Ty<'a>, Option<TyTypePredicate<'a>>) {
        return_type_and_type_predicate_from_annotation_with_resolver(
            parameters,
            return_type,
            |annotation| self.get_type_from_ts_type(program_id, &annotation.type_annotation),
        )
    }

    fn instantiate_signature_return_type(
        &self,
        program_id: ProgramId,
        return_type: Ty<'a>,
        mapper: &TypeMapper<'a>,
    ) -> Ty<'a> {
        let return_type = self.instantiate_type(return_type, mapper);
        self.normalize_instantiated_signature_return_type(program_id, return_type, 0)
    }

    fn resolve_call_signature_candidate(
        &self,
        program_id: ProgramId,
        signature: Signature<'a>,
        call_expression: &'a CallExpression<'a>,
        node_id: Option<NodeId>,
        require_applicable: bool,
    ) -> Option<ResolvedSignatureCandidate<'a>> {
        let function = signature.function(self.arena());
        let inference = self.infer_call_type_parameter_resolution(
            program_id,
            function,
            call_expression,
            node_id,
        );
        let instantiated = self.instantiate_signature_return_type(
            program_id,
            function.return_type,
            inference.mapper(),
        );

        if require_applicable
            && !self.is_call_signature_applicable(
                program_id,
                function,
                CallKind::Call(call_expression),
                node_id,
                inference.substitutions(),
            )
        {
            return None;
        }

        Some(ResolvedSignatureCandidate {
            signature,
            inference,
            return_type: instantiated,
        })
    }

    pub(crate) fn get_type_predicate_of_call_expression(
        &self,
        program_id: ProgramId,
        call_expression: &'a CallExpression<'a>,
    ) -> Option<TyTypePredicate<'a>> {
        let callee_type = self.get_type_of_expression_with_node(
            program_id,
            &call_expression.callee,
            Some(call_expression.node_id.get()),
            GetTypeFlags::CONTEXT_FREE,
        );
        self.get_signatures_of_type(callee_type, SignatureKind::Call)
            .into_iter()
            .filter_map(|signature| {
                self.resolve_call_signature_candidate(
                    program_id,
                    signature,
                    call_expression,
                    Some(call_expression.node_id.get()),
                    true,
                )
            })
            .find_map(|candidate| {
                candidate
                    .signature
                    .function(self.arena())
                    .type_predicate
                    .map(|predicate| {
                        self.instantiate_type_predicate(*predicate, candidate.inference.mapper())
                    })
            })
    }

    fn explicit_call_type_parameter_substitutions(
        &self,
        program_id: ProgramId,
        function: &'a TyFunction<'a>,
        call_kind: CallKind<'a>,
    ) -> TypeParameterSubstitutions<'a> {
        let type_arguments = call_kind.type_arguments();
        let flags = match call_kind {
            CallKind::Call(_) => SubstituteTypeFlags::NONE,
            CallKind::New(_) => SubstituteTypeFlags::FILL_UNRESOLVED_WITH_UNKNOWN,
        };

        let (mut substitutions, _) =
            self.explicit_type_parameter_substitutions(program_id, function, type_arguments);
        self.add_type_parameter_fallback_substitutions(function, &mut substitutions, flags);

        substitutions
    }

    pub(crate) fn explicit_type_parameter_substitutions(
        &self,
        program_id: ProgramId,
        function: &'a TyFunction<'a>,
        type_arguments: Option<&'a oxc_ast::ast::TSTypeParameterInstantiation<'a>>,
    ) -> (TypeParameterSubstitutions<'a>, Vec<&'a str>) {
        let mut substitutions = TypeParameterSubstitutions::new();
        let mut explicit_type_parameters = Vec::new();

        if let Some(type_arguments) = type_arguments {
            for (type_parameter, type_argument) in function
                .type_parameters
                .iter()
                .zip(type_arguments.params.iter())
            {
                substitutions.insert(
                    *type_parameter,
                    self.get_type_from_ts_type(program_id, type_argument),
                );
                explicit_type_parameters.push(type_parameter.name);
            }
        }

        (substitutions, explicit_type_parameters)
    }

    pub(crate) fn add_type_parameter_fallback_substitutions(
        &self,
        function: &TyFunction<'a>,
        substitutions: &mut TypeParameterSubstitutions<'a>,
        flags: SubstituteTypeFlags,
    ) {
        for type_parameter in &function.type_parameters {
            if substitutions.contains(*type_parameter) {
                continue;
            }
            if let Some(fallback_type) = type_parameter
                .default_type
                .or(type_parameter.constraint_type)
            {
                let mapper = substitutions.to_mapper(self.arena());
                substitutions.insert(
                    *type_parameter,
                    self.instantiate_type(fallback_type, &mapper),
                );
            }
        }

        if flags.fill_unresolved_with_unknown() {
            for type_parameter in &function.type_parameters {
                if !substitutions.contains(*type_parameter) {
                    substitutions.insert(*type_parameter, Ty::unknown());
                }
            }
        }
    }

    fn is_call_signature_applicable(
        &self,
        program_id: ProgramId,
        function: &TyFunction<'a>,
        call_kind: CallKind<'a>,
        node_id: Option<NodeId>,
        substitutions: &TypeParameterSubstitutions<'a>,
    ) -> bool {
        let type_arguments = call_kind.type_arguments();
        let type_argument_count =
            type_arguments.map_or(0, |type_arguments| type_arguments.params.len());
        if type_argument_count > function.type_parameters.len() {
            return false;
        }

        let arguments = match call_kind {
            CallKind::Call(call_expression) => &call_expression.arguments,
            CallKind::New(new_expression) => &new_expression.arguments,
        };
        let argument_count = arguments.len();

        let minimum_argument_count = function_minimum_argument_count(self.arena(), function);
        let maximum_argument_count = function_maximum_argument_count(self.arena(), function);

        let has_compatible_argument_count = argument_count >= minimum_argument_count
            && maximum_argument_count.is_none_or(|maximum| argument_count <= maximum);
        if !has_compatible_argument_count {
            return false;
        }

        self.arguments_are_assignable_to_parameters(
            program_id,
            function,
            arguments.iter().map(|argument| argument.as_expression()),
            node_id,
            substitutions,
        )
    }

    fn get_call_parameter_type_at(
        &self,
        function: &TyFunction<'a>,
        index: usize,
    ) -> Option<Ty<'a>> {
        function_parameter_type_at_call_index(self.arena(), function, index)
    }

    fn get_type_of_new_expression(
        &self,
        program_id: ProgramId,
        new_expression: &'a NewExpression<'a>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        let Expression::Identifier(identifier) = &new_expression.callee else {
            return Ty::error(self.arena(), TypeErrorKind::UnsupportedType);
        };

        let constructor_type = self
            .symbol_for_identifier_reference(program_id, identifier)
            .or_else(|| self.get_value_symbol_for_name(program_id, identifier.name.as_str()))
            .map(|symbol| {
                let base_type = self.get_type_of_symbol(symbol);
                if flags.context_free() {
                    base_type
                } else {
                    flow::get_flow_type_of_reference(
                        self,
                        self.identifier_node_ref(program_id, identifier),
                        symbol,
                        base_type,
                    )
                }
            });

        if let Some(constructor_type) = constructor_type
            && let TypeData::TypeQuery(query) = self.arena().type_data(constructor_type)
            && query.type_arguments.is_empty()
        {
            let mut type_arguments = new_expression
                .type_arguments
                .as_deref()
                .into_iter()
                .flat_map(|type_arguments| {
                    type_arguments.params.iter().map(|type_argument| {
                        self.get_type_argument_from_ts_type(program_id, type_argument)
                    })
                })
                .collect::<Vec<_>>();
            let explicit_type_argument_count = type_arguments.len();
            let implicit_display_type_argument_count =
                self.fill_default_type_arguments(program_id, query.name, &mut type_arguments);
            return self.type_reference_with_display_type_argument_count(
                program_id,
                query.name,
                type_arguments,
                explicit_type_argument_count + implicit_display_type_argument_count,
            );
        }

        if let Some(constructor_type) = constructor_type
            && let Some(constructed_type) = self.resolve_construct_signature_return_type(
                program_id,
                constructor_type,
                new_expression,
            )
        {
            return constructed_type;
        }

        Ty::type_reference(self.arena(), identifier.name.as_str(), std::iter::empty())
    }

    fn resolve_construct_signature_return_type(
        &self,
        program_id: ProgramId,
        constructor_type: Ty<'a>,
        new_expression: &'a NewExpression<'a>,
    ) -> Option<Ty<'a>> {
        let candidates = self.get_signatures_of_type_in_program(
            program_id,
            constructor_type,
            SignatureKind::Construct,
        );
        let applicable = candidates
            .iter()
            .filter_map(|signature| {
                self.resolve_construct_signature_candidate(
                    program_id,
                    *signature,
                    new_expression,
                    true,
                )
            })
            .collect::<Vec<_>>();

        self.choose_best_signature_candidate(applicable)
            .or_else(|| {
                candidates.first().and_then(|signature| {
                    self.resolve_construct_signature_candidate(
                        program_id,
                        *signature,
                        new_expression,
                        false,
                    )
                })
            })
            .map(ResolvedSignatureCandidate::into_return_type)
    }

    fn resolve_construct_signature_candidate(
        &self,
        program_id: ProgramId,
        signature: Signature<'a>,
        new_expression: &'a NewExpression<'a>,
        require_applicable: bool,
    ) -> Option<ResolvedSignatureCandidate<'a>> {
        let function = signature.function(self.arena());
        let inference =
            self.infer_construct_type_parameter_resolution(program_id, function, new_expression);

        if require_applicable
            && !self.is_call_signature_applicable(
                program_id,
                function,
                CallKind::New(new_expression),
                None,
                inference.substitutions(),
            )
        {
            return None;
        }

        let instantiated = self.instantiate_signature_return_type(
            program_id,
            function.return_type,
            inference.mapper(),
        );
        Some(ResolvedSignatureCandidate {
            signature,
            inference,
            return_type: instantiated,
        })
    }

    fn arguments_are_assignable_to_parameters(
        &self,
        program_id: ProgramId,
        function: &TyFunction<'a>,
        arguments: impl Iterator<Item = Option<&'a Expression<'a>>>,
        node_id: Option<NodeId>,
        substitutions: &TypeParameterSubstitutions<'a>,
    ) -> bool {
        let mapper = substitutions.to_mapper(self.arena());
        for (index, argument) in arguments.enumerate() {
            let Some(argument) = argument else {
                continue;
            };
            let Some(parameter_type) = self.get_call_parameter_type_at(function, index) else {
                return false;
            };
            let flags = if self.should_preserve_argument_literals_for_parameter_type(parameter_type)
            {
                GetTypeFlags::PRESERVE_LITERALS
            } else {
                GetTypeFlags::NONE
            };
            let parameter_type = self.instantiate_type(parameter_type, &mapper);
            let argument_type = self.get_type_of_call_argument_for_parameter(
                program_id,
                argument,
                node_id,
                parameter_type,
                flags,
            );
            if !self.is_assignable_to(argument_type, parameter_type) {
                return false;
            }
        }

        true
    }

    fn should_preserve_argument_literals_for_parameter_type(&self, parameter_type: Ty<'a>) -> bool {
        self.could_contain_type_variables(parameter_type)
            || match self.arena().type_data(parameter_type) {
                TypeData::StringLiteral(_)
                | TypeData::NumberLiteral(_)
                | TypeData::BooleanLiteral(_)
                | TypeData::BigIntLiteral(_) => true,
                TypeData::Union(union) => union
                    .types
                    .iter()
                    .any(|ty| self.should_preserve_argument_literals_for_parameter_type(*ty)),
                _ => false,
            }
    }

    fn get_property_type_of_named_type(
        &self,
        program_id: ProgramId,
        object_type: &Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let (class_name, is_static) = match self.arena().type_data(*object_type) {
            TypeData::TypeReference(reference) => {
                if let Some(ty) =
                    self.get_property_type_of_interface_type(program_id, reference, property_name)
                {
                    return Some(ty);
                }
                (reference.name, false)
            }
            // `typeof Class` value-side property access (statics).
            TypeData::TypeQuery(query) => (query.name, true),
            _ => return None,
        };
        let class_symbol = self.get_class_symbol_for_type(program_id, class_name)?;
        let (class_node_id, class) = self.get_class_for_symbol(class_symbol)?;
        self.get_class_member_type(
            class_symbol.program_id,
            class_node_id,
            class,
            property_name,
            is_static,
        )
    }

    fn get_property_type_of_interface_type(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let key = (
            program_id.index(),
            reference.name.to_string(),
            property_name.to_string(),
        );
        let stack = &self.interface_property_resolution_stack;
        let cycle_detected = {
            let mut stack = stack.borrow_mut();
            if stack.contains(&key) {
                true
            } else {
                stack.push(key.clone());
                false
            }
        };
        if cycle_detected {
            return Some(Ty::error(self.arena(), TypeErrorKind::UnresolvedMember));
        }

        let declarations = self.interface_declarations_for_type_name(program_id, reference.name);
        let result = self
            .get_property_type_of_interface_declarations(reference, property_name, &declarations)
            .or_else(|| {
                let (symbol, declaration) =
                    self.get_type_symbol_and_declaration_for_name(program_id, reference.name)?;
                self.get_property_type_of_interface_declaration(
                    symbol.program_id,
                    declaration,
                    reference,
                    property_name,
                )
            });

        {
            let mut stack = stack.borrow_mut();
            if let Some(position) = stack.iter().rposition(|active| active == &key) {
                stack.remove(position);
            }
        }

        result
    }

    fn get_property_type_of_interface_declarations(
        &self,
        reference: &TyTypeReference<'a>,
        property_name: &str,
        declarations: &[(ProgramId, &'a TSInterfaceDeclaration<'a>)],
    ) -> Option<Ty<'a>> {
        if declarations.is_empty() {
            return None;
        }

        for &(program_id, interface) in declarations {
            let substitutions = self.type_parameter_substitutions_for_reference(
                program_id,
                interface.type_parameters.as_deref(),
                reference,
            );
            let mapper = substitutions.to_mapper(self.arena());
            if let Some(ty) = self.get_interface_property_or_accessor_type(
                program_id,
                &interface.body.body,
                property_name,
            ) {
                return Some(self.instantiate_type(ty, &mapper));
            }
        }

        let method_signatures = declarations
            .iter()
            .copied()
            .flat_map(|(program_id, interface)| {
                let mapper = self.interface_member_mapper(
                    program_id,
                    interface.type_parameters.as_deref(),
                    reference,
                );
                self.get_interface_method_signatures(
                    program_id,
                    &interface.body.body,
                    property_name,
                    &mapper,
                )
            })
            .collect::<Vec<_>>();
        match method_signatures.as_slice() {
            [] => None,
            [signature] => Some(signature.ty),
            _ => Some(Ty::object_with_signatures(
                self.arena(),
                [],
                method_signatures,
            )),
        }
    }

    fn get_interface_property_or_accessor_type(
        &self,
        program_id: ProgramId,
        members: &'a [TSSignature<'a>],
        property_name: &str,
    ) -> Option<Ty<'a>> {
        if let Some(property) = members.iter().find_map(|signature| {
            let TSSignature::TSPropertySignature(property) = signature else {
                return None;
            };
            (self.resolved_property_key_name(program_id, &property.key) == Some(property_name))
                .then_some(property)
        }) {
            return Some(
                property
                    .type_annotation
                    .as_deref()
                    .map_or_else(Ty::any, |annotation| {
                        self.get_type_from_ts_type(program_id, &annotation.type_annotation)
                    }),
            );
        }

        for accessor_kind in [TSMethodSignatureKind::Get, TSMethodSignatureKind::Set] {
            if let Some(ty) = members.iter().find_map(|signature| {
                let TSSignature::TSMethodSignature(method) = signature else {
                    return None;
                };
                (method.kind == accessor_kind
                    && self.resolved_property_key_name(program_id, &method.key)
                        == Some(property_name))
                .then(|| self.get_type_of_ts_accessor_signature(program_id, method))
                .flatten()
            }) {
                return Some(ty);
            }
        }

        None
    }

    fn get_interface_method_signatures(
        &self,
        program_id: ProgramId,
        members: &'a [TSSignature<'a>],
        property_name: &str,
        mapper: &TypeMapper<'a>,
    ) -> Vec<Signature<'a>> {
        members
            .iter()
            .filter_map(|signature| {
                let TSSignature::TSMethodSignature(method) = signature else {
                    return None;
                };
                (method.kind == TSMethodSignatureKind::Method
                    && self.resolved_property_key_name(program_id, &method.key)
                        == Some(property_name))
                .then(|| {
                    self.instantiate_signature(
                        self.signature_from_ts_method_signature(program_id, method),
                        mapper,
                    )
                })
            })
            .collect()
    }

    fn get_property_type_of_interface_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        reference: &TyTypeReference<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let interface = match self.nodes(program_id).kind(declaration) {
            AstKind::TSInterfaceDeclaration(interface) => interface,
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                let AstKind::TSInterfaceDeclaration(interface) =
                    self.nodes(program_id).kind(parent_id)
                else {
                    return None;
                };
                interface
            }
            _ => return None,
        };
        let declarations = [(program_id, interface)];
        self.get_property_type_of_interface_declarations(reference, property_name, &declarations)
    }

    fn get_type_of_ts_accessor_signature(
        &self,
        program_id: ProgramId,
        method: &'a oxc_ast::ast::TSMethodSignature<'a>,
    ) -> Option<Ty<'a>> {
        match method.kind {
            TSMethodSignatureKind::Get => Some(
                self.get_type_from_ts_type_annotation(program_id, method.return_type.as_deref()),
            ),
            TSMethodSignatureKind::Set => Some(method.params.items.first().map_or_else(
                Ty::any,
                |parameter| {
                    self.get_type_from_ts_type_annotation(
                        program_id,
                        parameter.type_annotation.as_deref(),
                    )
                },
            )),
            TSMethodSignatureKind::Method => None,
        }
    }

    fn get_type_of_ts_method_signature_location(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        method: &'a oxc_ast::ast::TSMethodSignature<'a>,
    ) -> Ty<'a> {
        if let Some(ty) = self.get_type_of_ts_accessor_signature(program_id, method) {
            return ty;
        }

        let default_function = || {
            self.signature_from_ts_method_signature(program_id, method)
                .ty
        };
        let Some(method_name) = property_key_name_str(&method.key) else {
            return default_function();
        };

        let Some(current_interface) =
            self.nodes(program_id)
                .ancestor_kinds(node_id)
                .find_map(|kind| match kind {
                    AstKind::TSInterfaceDeclaration(interface) => Some(interface),
                    _ => None,
                })
        else {
            return default_function();
        };

        let current_type_arguments = self
            .type_parameters_from_declaration(
                program_id,
                current_interface.type_parameters.as_deref(),
            )
            .into_iter()
            .map(|type_parameter| Ty::type_reference(self.arena(), type_parameter.name, []))
            .collect::<Vec<_>>();

        let method_signatures = self
            .interface_declarations_for_type_name(program_id, current_interface.id.name.as_str())
            .into_iter()
            .flat_map(|(interface_program_id, interface)| {
                let substitutions = self.type_parameter_substitutions_for_type_arguments(
                    interface_program_id,
                    interface.type_parameters.as_deref(),
                    &current_type_arguments,
                );
                let mapper = substitutions.to_mapper(self.arena());
                interface.body.body.iter().filter_map(move |signature| {
                    let TSSignature::TSMethodSignature(candidate) = signature else {
                        return None;
                    };
                    (candidate.kind == TSMethodSignatureKind::Method
                        && property_key_name_str(&candidate.key) == Some(method_name))
                    .then(|| {
                        self.instantiate_signature(
                            self.signature_from_ts_method_signature(
                                interface_program_id,
                                candidate,
                            ),
                            &mapper,
                        )
                    })
                })
            })
            .collect::<Vec<_>>();

        match method_signatures.as_slice() {
            [] => {
                self.signature_from_ts_method_signature(program_id, method)
                    .ty
            }
            [signature] => signature.ty,
            _ => Ty::object_with_signatures(self.arena(), [], method_signatures),
        }
    }

    fn type_parameter_substitutions_for_reference(
        &self,
        program_id: ProgramId,
        type_parameters: Option<&'a oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        reference: &TyTypeReference<'a>,
    ) -> TypeParameterSubstitutions<'a> {
        self.type_parameter_substitutions_for_type_arguments(
            program_id,
            type_parameters,
            reference.type_arguments.as_slice(),
        )
    }

    fn interface_member_mapper(
        &self,
        program_id: ProgramId,
        type_parameters: Option<&'a oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        reference: &TyTypeReference<'a>,
    ) -> TypeMapper<'a> {
        let receiver = Ty::type_reference(
            self.arena(),
            reference.name,
            reference.type_arguments.iter().copied(),
        );
        self.type_parameter_substitutions_for_reference(program_id, type_parameters, reference)
            .to_mapper(self.arena())
            .with_prepend_mapping(self.arena(), Ty::this(), receiver)
    }

    fn type_parameter_substitutions_for_type_arguments(
        &self,
        program_id: ProgramId,
        type_parameters: Option<&'a oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        type_arguments: &[Ty<'a>],
    ) -> TypeParameterSubstitutions<'a> {
        let type_parameters = self.type_parameters_from_declaration(program_id, type_parameters);
        let mut substitutions =
            self.explicit_type_argument_substitutions(&type_parameters, type_arguments);

        self.add_default_type_argument_substitutions(
            &type_parameters,
            type_arguments.len(),
            &mut substitutions,
            |_| {},
        );

        substitutions
    }

    fn explicit_type_argument_substitutions(
        &self,
        type_parameters: &[TyTypeParameter<'a>],
        type_arguments: &[Ty<'a>],
    ) -> TypeParameterSubstitutions<'a> {
        let mut substitutions = TypeParameterSubstitutions::new();

        for (type_parameter, type_argument) in type_parameters.iter().zip(type_arguments.iter()) {
            substitutions.insert(*type_parameter, *type_argument);
        }

        substitutions
    }

    fn add_default_type_argument_substitutions(
        &self,
        type_parameters: &[TyTypeParameter<'a>],
        explicit_count: usize,
        substitutions: &mut TypeParameterSubstitutions<'a>,
        mut on_default: impl FnMut(Ty<'a>),
    ) {
        for type_parameter in type_parameters.iter().skip(explicit_count) {
            let Some(default_type) = type_parameter.default_type else {
                break;
            };
            let default_type = self.instantiate_type_parameter_default(
                default_type,
                type_parameters,
                substitutions,
            );
            substitutions.insert(*type_parameter, default_type);
            on_default(default_type);
        }
    }

    fn instantiate_type_parameter_default(
        &self,
        default_type: Ty<'a>,
        type_parameters: &[TyTypeParameter<'a>],
        substitutions: &TypeParameterSubstitutions<'a>,
    ) -> Ty<'a> {
        let mut default_substitutions = substitutions.clone();
        for unresolved in type_parameters {
            if !default_substitutions.contains(*unresolved) {
                default_substitutions.insert(*unresolved, Ty::any());
            }
        }
        let mapper = default_substitutions.to_mapper(self.arena());
        self.instantiate_type(default_type, &mapper)
    }

    fn type_parameters_from_declaration(
        &self,
        program_id: ProgramId,
        declaration: Option<&'a oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
    ) -> Vec<TyTypeParameter<'a>> {
        declaration.map_or_else(Vec::new, |declaration| {
            declaration
                .params
                .iter()
                .map(|parameter| self.type_parameter_from_ts_type_parameter(program_id, parameter))
                .collect()
        })
    }

    fn type_parameter_from_ts_type_parameter(
        &self,
        program_id: ProgramId,
        parameter: &'a TSTypeParameter<'a>,
    ) -> TyTypeParameter<'a> {
        let key = parameter
            .name
            .symbol_id
            .get()
            .map(|symbol_id| TypeParameterResolution::Symbol(SymbolRef::new(program_id, symbol_id)))
            .unwrap_or(TypeParameterResolution::Span(program_id, parameter.span));
        {
            let mut resolving_type_parameters = self.resolving_type_parameters.borrow_mut();
            if resolving_type_parameters.contains(&key) {
                return Ty::type_parameter(parameter.name.name.as_str(), None, None);
            }
            resolving_type_parameters.push(key);
        }

        let constraint = parameter
            .constraint
            .as_ref()
            .map(|constraint| self.get_type_from_ts_type(program_id, constraint));
        let default = parameter.default.as_ref().map(|default| {
            self.get_apparent_type_at_use(
                program_id,
                self.get_type_from_ts_type(program_id, default),
                0,
            )
        });

        self.resolving_type_parameters.borrow_mut().pop();

        Ty::type_parameter(parameter.name.name.as_str(), constraint, default)
    }

    pub fn get_class_symbol_for_type(
        &self,
        program_id: ProgramId,
        class_name: &str,
    ) -> Option<SymbolRef> {
        self.get_root_symbol(program_id, class_name)
            .and_then(|symbol| self.get_imported_symbol(symbol).or(Some(symbol)))
            .or_else(|| {
                self.store.entries().iter().find_map(|entry| {
                    self.get_root_symbol(entry.id(), class_name)
                        .and_then(|symbol| self.get_imported_symbol(symbol).or(Some(symbol)))
                })
            })
    }

    pub fn get_root_symbol(&self, program_id: ProgramId, name: &str) -> Option<SymbolRef> {
        self.semantic(program_id)
            .scoping()
            .get_root_binding(Ident::from(name))
            .map(|symbol_id| SymbolRef::new(program_id, symbol_id))
    }

    #[inline]
    pub(crate) fn symbol_for_identifier_reference(
        &self,
        program_id: ProgramId,
        identifier: &IdentifierReference<'_>,
    ) -> Option<SymbolRef> {
        identifier
            .reference_id
            .get()
            .and_then(|reference_id| {
                self.semantic(program_id)
                    .scoping()
                    .get_reference(reference_id)
                    .symbol_id()
            })
            .map(|symbol_id| SymbolRef::new(program_id, symbol_id))
    }

    fn interface_declarations_for_name(
        &self,
        type_name: &str,
    ) -> &'a [(ProgramId, &'a TSInterfaceDeclaration<'a>)] {
        if let Some(declarations) = self.interface_declarations_cache.borrow().get(type_name) {
            return declarations;
        }

        let declarations = self
            .arena()
            .vec_from_iter(self.store.entries().iter().flat_map(|entry| {
                let scoping = entry.semantic().scoping();
                scoping
                    .get_root_binding(Ident::from(type_name))
                    .into_iter()
                    .flat_map(move |symbol_id| {
                        scoping.symbol_declarations(symbol_id).filter_map(
                            move |node_id| match entry.semantic().nodes().kind(node_id) {
                                AstKind::TSInterfaceDeclaration(interface) => {
                                    Some((entry.id(), interface))
                                }
                                AstKind::BindingIdentifier(_) => {
                                    let parent_id = entry.semantic().nodes().parent_id(node_id);
                                    match entry.semantic().nodes().kind(parent_id) {
                                        AstKind::TSInterfaceDeclaration(interface) => {
                                            Some((entry.id(), interface))
                                        }
                                        _ => None,
                                    }
                                }
                                _ => None,
                            },
                        )
                    })
            }));
        let declarations = self.arena().alloc(declarations.into_boxed_slice());
        self.interface_declarations_cache
            .borrow_mut()
            .insert(type_name.to_string(), declarations);
        declarations
    }

    fn get_type_parameters_for_type(
        &self,
        program_id: ProgramId,
        type_name: &str,
    ) -> Option<Vec<TyTypeParameter<'a>>> {
        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, type_name)?;
        self.get_type_parameters_for_declaration(symbol.program_id, declaration)
    }

    fn get_type_parameters_for_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
    ) -> Option<Vec<TyTypeParameter<'a>>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSInterfaceDeclaration(interface) => {
                Some(self.type_parameters_from_declaration(
                    program_id,
                    interface.type_parameters.as_deref(),
                ))
            }
            AstKind::TSTypeAliasDeclaration(alias) => Some(
                self.type_parameters_from_declaration(program_id, alias.type_parameters.as_deref()),
            ),
            AstKind::Class(class) => Some(
                self.type_parameters_from_declaration(program_id, class.type_parameters.as_deref()),
            ),
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_type_parameters_for_declaration(program_id, parent_id)
            }
            _ => None,
        }
    }

    fn get_class_for_symbol(&self, symbol: SymbolRef) -> Option<(NodeId, &'a Class<'a>)> {
        self.semantic(symbol.program_id)
            .scoping()
            .symbol_declarations(symbol.symbol_id)
            .find_map(|declaration| self.class_declaration_at(symbol.program_id, declaration))
    }

    fn class_declaration_at(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
    ) -> Option<(NodeId, &'a Class<'a>)> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::Class(class) => Some((declaration, class)),
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                match self.nodes(program_id).kind(parent_id) {
                    AstKind::Class(class) => Some((parent_id, class)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn get_type_of_class_expression(&self, program_id: ProgramId, class: &'a Class<'a>) -> Ty<'a> {
        self.get_type_of_class_constructor(
            program_id,
            class,
            self.type_parameters_from_declaration(program_id, class.type_parameters.as_deref()),
            false,
        )
    }

    fn get_type_of_duplicate_class_declaration(
        &self,
        program_id: ProgramId,
        class: &'a Class<'a>,
    ) -> Ty<'a> {
        let type_parameters = self
            .class_base_type_arguments(program_id, class)
            .into_iter()
            .map(|type_argument| {
                let name = self
                    .arena()
                    .str(&type_argument.to_type_string(self.arena()));
                Ty::type_parameter_with_display_default(name, None, None, true)
            });
        self.get_type_of_class_constructor(program_id, class, type_parameters, true)
    }

    fn get_type_of_class_constructor(
        &self,
        program_id: ProgramId,
        class: &'a Class<'a>,
        type_parameters: impl IntoIterator<Item = TyTypeParameter<'a>>,
        display_type_parameters_as_arguments: bool,
    ) -> Ty<'a> {
        let class_node_id = class.node_id.get();
        let instance_type = Ty::object(
            self.arena(),
            class.body.body.iter().filter_map(|element| match element {
                ClassElement::MethodDefinition(method)
                    if !method.r#static && method.kind != MethodDefinitionKind::Constructor =>
                {
                    let name = property_key_name_str(&method.key)?;
                    Some(TyProperty {
                        name,
                        computed: false,
                        optional: false,
                        method: true,
                        readonly: false,
                        ty: self.get_type_of_method_definition(program_id, method, class_node_id),
                    })
                }
                ClassElement::PropertyDefinition(property) if !property.r#static => {
                    let name = property_key_name_str(&property.key)?;
                    Some(Ty::property(
                        name,
                        self.get_type_of_property_definition(
                            program_id,
                            property,
                            Some(class_node_id),
                        ),
                    ))
                }
                _ => None,
            }),
        );
        let constructor_parameters = class.body.body.iter().find_map(|element| {
            let ClassElement::MethodDefinition(method) = element else {
                return None;
            };
            (method.kind == MethodDefinitionKind::Constructor)
                .then(|| self.function_type_parameters(program_id, None, &method.value.params))
        });
        let constructor_type = Ty::function_with_type_predicate_and_display(
            self.arena(),
            type_parameters,
            constructor_parameters.unwrap_or_default(),
            instance_type,
            None,
            display_type_parameters_as_arguments,
        );

        Ty::object_with_signatures(
            self.arena(),
            [],
            [Signature::new(SignatureKind::Construct, constructor_type)],
        )
    }

    fn class_base_type_arguments(
        &self,
        program_id: ProgramId,
        class: &'a Class<'a>,
    ) -> Vec<Ty<'a>> {
        let Some(Expression::Identifier(identifier)) = class.super_class.as_ref() else {
            return Vec::new();
        };
        let mut type_arguments = class
            .super_type_arguments
            .as_ref()
            .into_iter()
            .flat_map(|arguments| arguments.params.iter())
            .map(|argument| self.get_type_argument_from_ts_type(program_id, argument))
            .collect::<Vec<_>>();
        self.fill_default_type_arguments(program_id, identifier.name.as_str(), &mut type_arguments);
        type_arguments
    }

    fn is_later_duplicate_class_declaration(
        &self,
        program_id: ProgramId,
        class: &'a Class<'a>,
    ) -> bool {
        let Some(identifier) = class.id.as_ref() else {
            return false;
        };
        let Some(symbol_id) = identifier.symbol_id.get() else {
            return false;
        };
        if self.is_in_exported_declaration(program_id, class.node_id.get()) {
            return false;
        }
        self.get_class_for_symbol(SymbolRef::new(program_id, symbol_id))
            .is_some_and(|(first_class_node_id, _)| first_class_node_id != class.node_id.get())
    }

    fn get_class_member_type(
        &self,
        program_id: ProgramId,
        class_node_id: NodeId,
        class: &'a Class<'a>,
        property_name: &str,
        is_static: bool,
    ) -> Option<Ty<'a>> {
        let resolution = ClassMemberResolution {
            program_id,
            class_name: class.id.as_ref().map_or_else(
                || "<anonymous>".to_string(),
                |identifier| identifier.name.to_string(),
            ),
            property_name: property_name.to_string(),
            is_static,
        };
        {
            let mut resolving_class_members = self.resolving_class_members.borrow_mut();
            if resolving_class_members.contains(&resolution) {
                return Some(Ty::error(self.arena(), TypeErrorKind::UnresolvedMember));
            }
            resolving_class_members.push(resolution);
        }

        let ty = class
            .body
            .body
            .iter()
            .find_map(|element| match element {
                ClassElement::MethodDefinition(method)
                    if property_key_name_str(&method.key) == Some(property_name) =>
                {
                    Some(self.get_type_of_method_definition(program_id, method, class_node_id))
                }
                ClassElement::PropertyDefinition(property)
                    if property.r#static == is_static
                        && property_key_name_str(&property.key) == Some(property_name) =>
                {
                    Some(self.get_type_of_property_definition(
                        program_id,
                        property,
                        Some(class_node_id),
                    ))
                }
                _ => None,
            })
            .or_else(|| {
                (!is_static).then_some(())?;
                class.body.body.iter().find_map(|element| {
                    let ClassElement::MethodDefinition(constructor) = element else {
                        return None;
                    };
                    if constructor.kind != MethodDefinitionKind::Constructor {
                        return None;
                    }
                    constructor.value.params.items.iter().find_map(|parameter| {
                        if !parameter.has_modifier()
                            || binding_pattern_to_parameter_name(self.arena(), &parameter.pattern)
                                != property_name
                        {
                            return None;
                        }
                        let ty = self.get_type_from_ts_type_annotation(
                            program_id,
                            parameter.type_annotation.as_deref(),
                        );
                        Some(if parameter.optional {
                            ty.or_undefined(self.arena())
                        } else {
                            ty
                        })
                    })
                })
            });

        self.resolving_class_members.borrow_mut().pop();
        ty
    }

    /// Resolve the type of a method definition on a class.
    /// Getters can turn into non-function types, but generally this returns a function type.
    fn get_type_of_method_definition(
        &self,
        program_id: ProgramId,
        method: &'a MethodDefinition<'a>,
        class_node_id: NodeId,
    ) -> Ty<'a> {
        debug_assert!(matches!(
            self.semantic(program_id).nodes().kind(class_node_id),
            AstKind::Class(_),
        ));

        let inferred_method_type = self.get_type_of_function_signature_with_node(
            program_id,
            FunctionKind::Function(&method.value),
            Some(class_node_id),
        );

        // For getters, the function type like `() => X` should just collapse into `X` to hide the fact that it's
        // actually a functional call (since it's just accessed like a property)
        if matches!(method.kind, MethodDefinitionKind::Get)
            && let TypeData::Function(func) = self.arena().type_data(inferred_method_type)
        {
            return func.return_type;
        }

        inferred_method_type
    }

    /// Resolve a class field's declared or inferred type.
    /// Class member lookups and declaration records use this to agree on annotation-first behavior.
    fn get_type_of_property_definition(
        &self,
        program_id: ProgramId,
        property: &'a PropertyDefinition<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        property.type_annotation.as_deref().map_or_else(
            || {
                property.value.as_ref().map_or_else(Ty::any, |value| {
                    self.get_type_of_expression_with_node(
                        program_id,
                        value,
                        node_id,
                        GetTypeFlags::NONE,
                    )
                })
            },
            |annotation| self.get_type_from_ts_type_annotation(program_id, Some(annotation)),
        )
    }

    /// Infer an unannotated formal parameter from the callback type expected by its call site.
    /// This lets callback bodies use parameter property types before broader inference exists.
    fn get_contextual_type_of_formal_parameter(
        &self,
        program_id: ProgramId,
        parameter_node_id: NodeId,
        parameter: &FormalParameter<'a>,
    ) -> Option<Ty<'a>> {
        let nodes = self.nodes(program_id);
        let (function_span, parameter_index) =
            nodes
                .ancestors(parameter_node_id)
                .find_map(|node| match node.kind() {
                    AstKind::Function(function) => function
                        .params
                        .items
                        .iter()
                        .position(|item| item.span == parameter.span)
                        .map(|index| (function.span, index)),
                    AstKind::ArrowFunctionExpression(function) => function
                        .params
                        .items
                        .iter()
                        .position(|item| item.span == parameter.span)
                        .map(|index| (function.span, index)),
                    _ => None,
                })?;

        let contextual_type = self.get_contextual_type_of_function_expression(
            program_id,
            parameter_node_id,
            function_span,
        )?;
        let callback_function = self
            .get_signatures_of_type_in_program(program_id, contextual_type, SignatureKind::Call)
            .into_iter()
            .next()?
            .function(self.arena());
        callback_function
            .parameters
            .get(parameter_index)
            .map(|parameter| self.get_apparent_type_at_use(program_id, parameter.ty, 0))
    }

    fn get_apparent_contextual_parameter_type(&self, program_id: ProgramId, ty: Ty<'a>) -> Ty<'a> {
        self.get_apparent_conditional_type_at_use(program_id, ty, false)
    }

    fn get_apparent_declared_parameter_type(&self, program_id: ProgramId, ty: Ty<'a>) -> Ty<'a> {
        self.get_apparent_conditional_type_at_use(program_id, ty, true)
    }

    fn get_apparent_conditional_type_at_use(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        expand_concrete_arguments: bool,
    ) -> Ty<'a> {
        if let TypeData::TypeReference(reference) = self.arena().type_data(ty)
            && self.is_conditional_type_alias_reference(program_id, reference)
            && let Some((expanded_program_id, expanded)) = if expand_concrete_arguments {
                self.get_concrete_conditional_type_alias_reference_type(program_id, reference)
            } else {
                self.get_conditional_type_alias_reference_type(program_id, reference)
            }
        {
            if matches!(self.arena().type_data(expanded), TypeData::Conditional(_)) {
                let apparent =
                    self.apparent_type_for_conditional_match(expanded_program_id, expanded, 0);
                return if matches!(self.arena().type_data(apparent), TypeData::Conditional(_)) {
                    ty
                } else {
                    apparent
                };
            }
            return expanded;
        }

        ty
    }

    fn get_conditional_type_alias_reference_type(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> Option<(ProgramId, Ty<'a>)> {
        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)?;
        self.get_conditional_type_alias_reference_type_with_arguments(
            &reference.type_arguments,
            symbol,
            declaration,
        )
    }

    fn get_concrete_conditional_type_alias_reference_type(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> Option<(ProgramId, Ty<'a>)> {
        let expanded_type_arguments = reference
            .type_arguments
            .iter()
            .map(|ty| self.expand_type_at_use(program_id, *ty, 0))
            .collect::<Vec<_>>();
        if expanded_type_arguments
            .iter()
            .any(|ty| self.could_contain_type_variables(*ty))
        {
            return None;
        }
        let (symbol, declaration) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)?;
        self.get_conditional_type_alias_reference_type_with_arguments(
            &expanded_type_arguments,
            symbol,
            declaration,
        )
    }

    fn get_conditional_type_alias_reference_type_with_arguments(
        &self,
        type_arguments: &[Ty<'a>],
        symbol: SymbolRef,
        declaration: NodeId,
    ) -> Option<(ProgramId, Ty<'a>)> {
        self.get_conditional_type_alias_declaration_type(
            symbol.program_id,
            declaration,
            type_arguments,
        )
        .map(|ty| (symbol.program_id, ty))
    }

    fn get_conditional_type_alias_declaration_type(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias)
                if matches!(alias.type_annotation, TSType::TSConditionalType(_)) =>
            {
                let substitutions = self.type_parameter_substitutions_for_type_arguments(
                    program_id,
                    alias.type_parameters.as_deref(),
                    type_arguments,
                );
                let mapper = substitutions.to_mapper(self.arena());
                Some(self.instantiate_type(
                    self.get_type_from_ts_type(program_id, &alias.type_annotation),
                    &mapper,
                ))
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_conditional_type_alias_declaration_type(
                    program_id,
                    parent_id,
                    type_arguments,
                )
            }
            _ => None,
        }
    }

    fn get_apparent_type_at_use(&self, program_id: ProgramId, ty: Ty<'a>, depth: usize) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::TypeReference(_) => {
                self.get_apparent_contextual_parameter_type(program_id, ty)
            }
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.get_apparent_type_at_use(program_id, *ty, depth + 1)),
            ),
            TypeData::Function(function) => Ty::function_with_type_predicate_and_display(
                self.arena(),
                function.type_parameters.iter().copied(),
                function.parameters.iter().map(|parameter| {
                    let ty = self.get_apparent_type_at_use(program_id, parameter.ty, depth + 1);
                    if parameter.rest {
                        Ty::rest_parameter(parameter.name, ty)
                    } else if parameter.optional {
                        Ty::optional_parameter(parameter.name, ty)
                    } else {
                        Ty::parameter(parameter.name, ty)
                    }
                }),
                self.get_apparent_type_at_use(program_id, function.return_type, depth + 1),
                function.type_predicate.copied(),
                function.display_type_parameters_as_arguments,
            ),
            _ => ty,
        }
    }

    fn is_conditional_type_alias_reference(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> bool {
        let Some((symbol, declaration)) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)
        else {
            return false;
        };
        self.is_conditional_type_alias_declaration(symbol.program_id, declaration)
    }

    fn is_conditional_type_alias_declaration(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
    ) -> bool {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias) => {
                matches!(alias.type_annotation, TSType::TSConditionalType(_))
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.is_conditional_type_alias_declaration(program_id, parent_id)
            }
            _ => false,
        }
    }

    fn get_contextual_type_of_function_expression(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        function_span: Span,
    ) -> Option<Ty<'a>> {
        self.get_contextual_type_of_call_argument(program_id, node_id, function_span)
            .or_else(|| {
                self.get_contextual_type_of_construct_argument(program_id, node_id, function_span)
            })
            .or_else(|| {
                self.get_contextual_type_of_object_property_value(
                    program_id,
                    node_id,
                    function_span,
                )
            })
            .or_else(|| {
                self.get_contextual_type_of_array_element(program_id, node_id, function_span)
            })
            .or_else(|| {
                self.get_contextual_type_of_binding_initializer(program_id, node_id, function_span)
            })
            .or_else(|| {
                self.get_contextual_type_of_return_expression(program_id, node_id, function_span)
            })
    }

    fn get_contextual_type_of_call_argument(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        function_span: Span,
    ) -> Option<Ty<'a>> {
        let call_expression =
            self.nodes(program_id)
                .ancestors(node_id)
                .find_map(|node| match node.kind() {
                    AstKind::CallExpression(call_expression) => Some(call_expression),
                    _ => None,
                })?;
        let argument_index = call_expression.arguments.iter().position(|argument| {
            argument
                .as_expression()
                .is_some_and(|expression| expression.span() == function_span)
        })?;

        let callee_type = self.get_type_of_expression_with_node(
            program_id,
            &call_expression.callee,
            Some(node_id),
            GetTypeFlags::NONE,
        );
        let callee_signature = self
            .get_signatures_of_type_in_program(program_id, callee_type, SignatureKind::Call)
            .into_iter()
            .next()?;
        let callee_function = callee_signature.function(self.arena());
        let parameter_type = self.get_call_parameter_type_at(callee_function, argument_index)?;
        let substitutions = self.explicit_call_type_parameter_substitutions(
            program_id,
            callee_function,
            CallKind::Call(call_expression),
        );
        let mapper = substitutions.to_mapper(self.arena());
        Some(self.instantiate_type(parameter_type, &mapper))
    }

    fn get_contextual_type_of_construct_argument(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        function_span: Span,
    ) -> Option<Ty<'a>> {
        let new_expression =
            self.nodes(program_id)
                .ancestors(node_id)
                .find_map(|node| match node.kind() {
                    AstKind::NewExpression(new_expression) => Some(new_expression),
                    _ => None,
                })?;
        let argument_index = new_expression.arguments.iter().position(|argument| {
            argument
                .as_expression()
                .is_some_and(|expression| expression.span() == function_span)
        })?;

        let callee_type = self.get_type_of_expression_with_node(
            program_id,
            &new_expression.callee,
            Some(node_id),
            GetTypeFlags::NONE,
        );
        let construct_signature = self
            .get_signatures_of_type_in_program(program_id, callee_type, SignatureKind::Construct)
            .into_iter()
            .next()?;
        let construct_function = construct_signature.function(self.arena());
        let parameter_type = self.get_call_parameter_type_at(construct_function, argument_index)?;
        let substitutions = self.explicit_call_type_parameter_substitutions(
            program_id,
            construct_function,
            CallKind::New(new_expression),
        );
        let mapper = substitutions.to_mapper(self.arena());
        Some(self.instantiate_type(parameter_type, &mapper))
    }

    fn get_contextual_type_of_object_property_value(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        value_span: Span,
    ) -> Option<Ty<'a>> {
        let mut property_name = None;
        let mut object_expression = None;

        if let AstKind::ObjectProperty(property) = self.node_kind(NodeRef::new(program_id, node_id))
            && property.value.span() == value_span
        {
            property_name = property_key_name_str(&property.key);
        }

        for ancestor in self.nodes(program_id).ancestors(node_id) {
            match ancestor.kind() {
                AstKind::ObjectProperty(property) if property.value.span() == value_span => {
                    property_name = property_key_name_str(&property.key);
                }
                AstKind::ObjectExpression(object) if property_name.is_some() => {
                    object_expression = Some(object);
                    break;
                }
                _ => {}
            }
        }

        let property_name = property_name?;
        let object = object_expression?;
        let object_context = self
            .get_contextual_type_of_object_property_value_from_intra_expression(
                program_id, node_id, object, value_span,
            )
            .or_else(|| {
                self.get_contextual_type_of_object_expression(program_id, node_id, object)
            })?;

        self.get_destructured_property_type(program_id, object_context, property_name)
    }

    fn get_contextual_type_of_object_expression(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        object: &'a ObjectExpression<'a>,
    ) -> Option<Ty<'a>> {
        self.get_contextual_type_of_call_argument(program_id, node_id, object.span)
            .or_else(|| {
                self.nodes(program_id)
                    .ancestors(node_id)
                    .find_map(|node| match node.kind() {
                        AstKind::VariableDeclarator(declarator)
                            if declarator
                                .init
                                .as_ref()
                                .is_some_and(|initializer| initializer.span() == object.span) =>
                        {
                            declarator.type_annotation.as_deref().map(|annotation| {
                                self.get_type_from_ts_type_annotation(program_id, Some(annotation))
                            })
                        }
                        AstKind::PropertyDefinition(property)
                            if property
                                .value
                                .as_ref()
                                .is_some_and(|initializer| initializer.span() == object.span) =>
                        {
                            property.type_annotation.as_deref().map(|annotation| {
                                self.get_type_from_ts_type_annotation(program_id, Some(annotation))
                            })
                        }
                        _ => None,
                    })
            })
            .or_else(|| {
                self.get_contextual_type_of_object_property_value(program_id, node_id, object.span)
            })
    }

    fn get_contextual_this_type_of_object_literal_method(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
    ) -> Option<Ty<'a>> {
        let mut function_span = None;
        let mut is_object_method = false;

        for ancestor in self.nodes(program_id).ancestors(node_id) {
            match ancestor.kind() {
                AstKind::Function(function) if function_span.is_none() => {
                    function_span = Some(function.span);
                }
                AstKind::ObjectProperty(property)
                    if function_span.is_some_and(|span| property.value.span() == span) =>
                {
                    is_object_method = true;
                }
                AstKind::ObjectExpression(object) if is_object_method => {
                    return self
                        .get_contextual_type_of_object_expression(program_id, node_id, object);
                }
                _ => {}
            }
        }

        None
    }

    fn get_contextual_type_of_object_property_value_from_intra_expression(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        object: &'a ObjectExpression<'a>,
        current_value_span: Span,
    ) -> Option<Ty<'a>> {
        let call_expression = self.nodes(program_id).ancestors(node_id).find_map(|node| {
            let AstKind::CallExpression(call_expression) = node.kind() else {
                return None;
            };
            call_expression
                .arguments
                .iter()
                .any(|argument| {
                    argument
                        .as_expression()
                        .is_some_and(|expression| expression.span() == object.span)
                })
                .then_some(call_expression)
        })?;
        let argument_index = call_expression.arguments.iter().position(|argument| {
            argument
                .as_expression()
                .is_some_and(|expression| expression.span() == object.span)
        })?;

        let callee_type = self.get_type_of_expression_with_node(
            program_id,
            &call_expression.callee,
            Some(node_id),
            GetTypeFlags::NONE,
        );
        let callee_signature = self
            .get_signatures_of_type_in_program(program_id, callee_type, SignatureKind::Call)
            .into_iter()
            .next()?;
        let callee_function = callee_signature.function(self.arena());
        let parameter_type = self.get_call_parameter_type_at(callee_function, argument_index)?;

        let argument_types = call_expression
            .arguments
            .iter()
            .enumerate()
            .filter_map(|(index, argument)| {
                let argument = argument.as_expression()?;
                let argument_type = if argument.span() == object.span {
                    self.get_type_of_object_expression_excluding_property_value(
                        program_id,
                        object,
                        current_value_span,
                    )
                } else {
                    let parameter_type = self.get_call_parameter_type_at(callee_function, index);
                    let flags =
                        if parameter_type.is_some_and(|ty| self.could_contain_type_variables(ty)) {
                            GetTypeFlags::PRESERVE_LITERALS
                        } else {
                            GetTypeFlags::NONE
                        };
                    self.get_type_of_expression_with_node(
                        program_id,
                        argument,
                        Some(node_id),
                        flags,
                    )
                };
                Some((index, argument_type))
            })
            .collect::<Vec<_>>();

        let inference = self.infer_call_type_parameter_resolution_from_argument_types(
            program_id,
            callee_function,
            call_expression.type_arguments.as_deref(),
            argument_types,
        );
        Some(self.instantiate_type(parameter_type, inference.mapper()))
    }

    fn get_type_of_object_expression_excluding_property_value(
        &self,
        program_id: ProgramId,
        object: &'a ObjectExpression<'a>,
        excluded_value_span: Span,
    ) -> Ty<'a> {
        Ty::object(
            self.arena(),
            object.properties.iter().filter_map(|property| {
                let ObjectPropertyKind::ObjectProperty(property) = property else {
                    return None;
                };
                if property.value.span() == excluded_value_span {
                    return None;
                }
                let name = property_key_name_str(&property.key)?;
                let ty = self.get_type_of_expression_with_node(
                    program_id,
                    &property.value,
                    None,
                    GetTypeFlags::NONE,
                );
                Some(Ty::property(name, ty))
            }),
        )
    }

    fn get_contextual_type_of_array_element(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        value_span: Span,
    ) -> Option<Ty<'a>> {
        let (array, element_index) =
            self.nodes(program_id).ancestors(node_id).find_map(|node| {
                let AstKind::ArrayExpression(array) = node.kind() else {
                    return None;
                };
                array
                    .elements
                    .iter()
                    .position(|element| {
                        array_expression_element_span(element)
                            .is_some_and(|element_span| element_span.contains_inclusive(value_span))
                    })
                    .map(|index| (array, index))
            })?;

        self.get_contextual_type_of_array_element_from_intra_expression(
            program_id,
            node_id,
            array,
            element_index,
        )
        .or_else(|| {
            let array_context =
                self.get_contextual_type_of_call_argument(program_id, node_id, array.span)?;
            self.get_contextual_type_of_array_element_at(program_id, array_context, element_index)
        })
    }

    fn get_contextual_type_of_array_element_from_intra_expression(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        array: &'a ArrayExpression<'a>,
        element_index: usize,
    ) -> Option<Ty<'a>> {
        let call_expression = self.nodes(program_id).ancestors(node_id).find_map(|node| {
            let AstKind::CallExpression(call_expression) = node.kind() else {
                return None;
            };
            call_expression
                .arguments
                .iter()
                .any(|argument| {
                    argument
                        .as_expression()
                        .is_some_and(|expression| expression.span() == array.span)
                })
                .then_some(call_expression)
        })?;
        let argument_index = call_expression.arguments.iter().position(|argument| {
            argument
                .as_expression()
                .is_some_and(|expression| expression.span() == array.span)
        })?;

        let callee_type = self.get_type_of_expression_with_node(
            program_id,
            &call_expression.callee,
            Some(node_id),
            GetTypeFlags::NONE,
        );
        let callee_signature = self
            .get_signatures_of_type_in_program(program_id, callee_type, SignatureKind::Call)
            .into_iter()
            .next()?;
        let callee_function = callee_signature.function(self.arena());
        let parameter_type = self.get_call_parameter_type_at(callee_function, argument_index)?;

        let argument_types = call_expression
            .arguments
            .iter()
            .enumerate()
            .filter_map(|(index, argument)| {
                let argument = argument.as_expression()?;
                let argument_type = if argument.span() == array.span {
                    self.get_type_of_array_expression_as_tuple_excluding_element(
                        program_id,
                        array,
                        element_index,
                    )
                } else {
                    let parameter_type = self.get_call_parameter_type_at(callee_function, index);
                    let flags =
                        if parameter_type.is_some_and(|ty| self.could_contain_type_variables(ty)) {
                            GetTypeFlags::PRESERVE_LITERALS
                        } else {
                            GetTypeFlags::NONE
                        };
                    self.get_type_of_expression_with_node(
                        program_id,
                        argument,
                        Some(node_id),
                        flags,
                    )
                };
                Some((index, argument_type))
            })
            .collect::<Vec<_>>();
        let inference = self.infer_call_type_parameter_resolution_from_argument_types(
            program_id,
            callee_function,
            call_expression.type_arguments.as_deref(),
            argument_types,
        );
        let array_context = self.instantiate_type(parameter_type, inference.mapper());
        self.get_contextual_type_of_array_element_at(program_id, array_context, element_index)
    }

    pub(crate) fn get_type_of_call_argument_for_parameter(
        &self,
        program_id: ProgramId,
        argument: &'a Expression<'a>,
        node_id: Option<NodeId>,
        parameter_type: Ty<'a>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        if let Expression::ArrayExpression(array) = argument
            && matches!(
                self.arena()
                    .type_data(self.expand_type_at_use(program_id, parameter_type, 0)),
                TypeData::Tuple(_)
            )
        {
            return self.get_type_of_array_expression_as_tuple_for_call_argument(
                program_id, array, node_id, flags,
            );
        }

        self.get_type_of_expression_with_node(program_id, argument, node_id, flags)
    }

    pub(crate) fn get_type_of_array_expression_as_tuple_for_call_argument(
        &self,
        program_id: ProgramId,
        array: &'a ArrayExpression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        self.get_type_of_array_expression_as_tuple_with_excluded_element(
            program_id, array, None, node_id, flags,
        )
    }

    fn get_type_of_array_expression_as_tuple_excluding_element(
        &self,
        program_id: ProgramId,
        array: &'a ArrayExpression<'a>,
        excluded_index: usize,
    ) -> Ty<'a> {
        self.get_type_of_array_expression_as_tuple_with_excluded_element(
            program_id,
            array,
            Some(excluded_index),
            None,
            GetTypeFlags::NONE,
        )
    }

    fn get_type_of_array_expression_as_tuple_with_excluded_element(
        &self,
        program_id: ProgramId,
        array: &'a ArrayExpression<'a>,
        excluded_index: Option<usize>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        Ty::tuple(
            self.arena(),
            array
                .elements
                .iter()
                .enumerate()
                .map(|(index, element)| {
                    if excluded_index == Some(index) {
                        TupleElement::Regular(Ty::any())
                    } else {
                        TupleElement::Regular(self.get_type_of_array_expression_element(
                            program_id,
                            element,
                            node_id,
                            ExpressionCheckContext::new(flags),
                        ))
                    }
                })
                .collect(),
        )
    }

    fn get_contextual_type_of_array_element_at(
        &self,
        program_id: ProgramId,
        array_context: Ty<'a>,
        element_index: usize,
    ) -> Option<Ty<'a>> {
        let array_context = self.expand_type_at_use(program_id, array_context, 0);
        match self.arena().type_data(array_context) {
            TypeData::Array(array) => Some(array.element_type),
            TypeData::Tuple(_) => {
                tuple_element_type_at_index(self.arena(), array_context, element_index)
            }
            TypeData::Union(union) => {
                let element_types = union
                    .types
                    .iter()
                    .filter_map(|ty| {
                        self.get_contextual_type_of_array_element_at(program_id, *ty, element_index)
                    })
                    .collect::<Vec<_>>();
                (!element_types.is_empty()).then(|| Ty::union(self.arena(), element_types))
            }
            _ => None,
        }
    }

    fn get_contextual_type_of_binding_initializer(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        function_span: Span,
    ) -> Option<Ty<'a>> {
        self.nodes(program_id)
            .ancestors_enumerated(node_id)
            .find_map(|(ancestor_id, node)| match node.kind() {
                AstKind::FormalParameter(parameter) => {
                    binding_pattern_default_initializer_symbol_id(&parameter.pattern, function_span)
                        .and_then(|symbol_id| {
                            self.get_type_of_binding_pattern(
                                program_id,
                                ancestor_id,
                                BindingPatternKind::FormalParameter(parameter),
                                symbol_id,
                            )
                        })
                }
                AstKind::VariableDeclarator(declarator) => {
                    binding_pattern_default_initializer_symbol_id(&declarator.id, function_span)
                        .and_then(|symbol_id| {
                            self.get_type_of_binding_pattern(
                                program_id,
                                ancestor_id,
                                BindingPatternKind::VariableDeclarator(declarator),
                                symbol_id,
                            )
                        })
                }
                _ => None,
            })
    }

    fn get_contextual_type_of_return_expression(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        function_span: Span,
    ) -> Option<Ty<'a>> {
        let mut matching_return_seen = false;
        for ancestor in self.nodes(program_id).ancestors(node_id) {
            match ancestor.kind() {
                AstKind::ReturnStatement(statement)
                    if statement
                        .argument
                        .as_ref()
                        .is_some_and(|argument| argument.span() == function_span) =>
                {
                    matching_return_seen = true;
                }
                AstKind::Function(function) if matching_return_seen => {
                    return function.return_type.as_deref().map(|annotation| {
                        self.get_type_from_ts_type_annotation(program_id, Some(annotation))
                    });
                }
                AstKind::ArrowFunctionExpression(function) if matching_return_seen => {
                    return function.return_type.as_deref().map(|annotation| {
                        self.get_type_from_ts_type_annotation(program_id, Some(annotation))
                    });
                }
                _ => {}
            }
        }
        None
    }

    fn get_type_of_function_signature_with_node(
        &self,
        program_id: ProgramId,
        function: FunctionKind<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let contextual_function = node_id
            .and_then(|node_id| {
                self.get_contextual_type_of_function_expression(
                    program_id,
                    node_id,
                    function.span(),
                )
            })
            .and_then(|contextual_type| {
                self.get_signatures_of_type_in_program(
                    program_id,
                    contextual_type,
                    SignatureKind::Call,
                )
                .into_iter()
                .next()
            })
            .map(|signature| signature.function(self.arena()));
        let type_parameters =
            self.type_parameters_from_declaration(program_id, function.type_parameters());
        let parameters = self.function_signature_parameters_with_context(
            program_id,
            function.parameters(),
            contextual_function,
        );
        let annotated_return_type = function.annotated_return_type();
        let return_type = match annotated_return_type {
            Some(annotation) => self.get_type_from_ts_type_annotation(program_id, Some(annotation)),
            None => self.infer_function_return_type(program_id, function, node_id),
        };

        let (return_type, type_predicate) = match annotated_return_type {
            Some(annotation) => self.return_type_and_type_predicate_from_annotation(
                program_id,
                &parameters,
                Some(annotation),
            ),
            None => (return_type, None),
        };

        Ty::function_with_type_predicate(
            self.arena(),
            type_parameters,
            parameters,
            return_type,
            type_predicate,
        )
    }

    fn function_signature_parameters(
        &self,
        program_id: ProgramId,
        params: &'a FormalParameters<'a>,
    ) -> Vec<TyParameter<'a>> {
        self.function_signature_parameters_with_context(program_id, params, None)
    }

    fn function_type_parameters(
        &self,
        program_id: ProgramId,
        this_param: Option<&'a TSThisParameter<'a>>,
        params: &'a FormalParameters<'a>,
    ) -> Vec<TyParameter<'a>> {
        this_param
            .iter()
            .map(|parameter| {
                Ty::parameter(
                    "this",
                    self.get_type_from_ts_type_annotation(
                        program_id,
                        parameter.type_annotation.as_deref(),
                    ),
                )
            })
            .chain(
                params
                    .items
                    .iter()
                    .map(|parameter| self.function_signature_parameter(program_id, parameter)),
            )
            .chain(
                params
                    .rest
                    .iter()
                    .map(|parameter| self.function_signature_rest_parameter(program_id, parameter)),
            )
            .collect()
    }

    fn function_signature_parameters_with_context(
        &self,
        program_id: ProgramId,
        params: &'a FormalParameters<'a>,
        contextual_function: Option<&'a TyFunction<'a>>,
    ) -> Vec<TyParameter<'a>> {
        params
            .items
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                self.function_signature_parameter_with_context(
                    program_id,
                    parameter,
                    contextual_function.and_then(|function| function.parameters.get(index)),
                )
            })
            .chain(
                params
                    .rest
                    .iter()
                    .map(|parameter| self.function_signature_rest_parameter(program_id, parameter)),
            )
            .collect()
    }

    fn function_signature_parameter(
        &self,
        program_id: ProgramId,
        parameter: &'a FormalParameter<'a>,
    ) -> TyParameter<'a> {
        let name = binding_pattern_to_parameter_name(self.arena(), &parameter.pattern);
        let ty =
            self.get_type_from_ts_type_annotation(program_id, parameter.type_annotation.as_deref());
        if parameter.optional {
            Ty::optional_parameter(name, ty)
        } else {
            Ty::parameter(name, ty)
        }
    }

    fn function_signature_parameter_with_context(
        &self,
        program_id: ProgramId,
        parameter: &'a FormalParameter<'a>,
        contextual_parameter: Option<&TyParameter<'a>>,
    ) -> TyParameter<'a> {
        if parameter.type_annotation.is_some() {
            return self.function_signature_parameter(program_id, parameter);
        }

        let name = binding_pattern_to_parameter_name(self.arena(), &parameter.pattern);
        let ty = contextual_parameter.map_or_else(Ty::any, |parameter| {
            self.get_apparent_contextual_parameter_type(program_id, parameter.ty)
        });
        if parameter.optional {
            Ty::optional_parameter(name, ty)
        } else {
            Ty::parameter(name, ty)
        }
    }

    fn function_signature_rest_parameter(
        &self,
        program_id: ProgramId,
        parameter: &'a FormalParameterRest<'a>,
    ) -> TyParameter<'a> {
        let name = binding_pattern_to_parameter_name(self.arena(), &parameter.rest.argument);
        Ty::rest_parameter(
            name,
            self.get_type_from_ts_type_annotation(program_id, parameter.type_annotation.as_deref()),
        )
    }

    fn get_parameter_type_from_ts_type_annotation(
        &self,
        program_id: ProgramId,
        type_annotation: Option<&'a TSTypeAnnotation<'a>>,
    ) -> Ty<'a> {
        let ty = self.get_type_from_ts_type_annotation(program_id, type_annotation);
        self.get_apparent_type_at_use(program_id, ty, 0)
    }

    pub(crate) fn get_async_function_return_type(
        &self,
        program_id: ProgramId,
        return_type: Ty<'a>,
    ) -> Ty<'a> {
        let promise_type = self.get_global_promise_type(program_id);
        match self.arena().type_data(promise_type) {
            TypeData::TypeReference(reference) => {
                // TODO(correctness): TypeScript wraps async returns with Promise<Awaited<T>>.
                Ty::type_reference(self.arena(), reference.name, [return_type])
            }
            TypeData::Any | TypeData::Error(_) => promise_type,
            _ => Ty::error(self.arena(), TypeErrorKind::MissingGlobalType),
        }
    }

    pub fn get_imported_symbol(&self, symbol: SymbolRef) -> Option<SymbolRef> {
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        let declaration_ref = NodeRef::new(symbol.program_id, declaration);
        let imported_name = match self.node_kind(declaration_ref) {
            AstKind::ImportSpecifier(specifier) => specifier.imported.name().to_string(),
            AstKind::ImportDefaultSpecifier(_) => "default".to_string(),
            _ => return None,
        };
        let AstKind::ImportDeclaration(import_declaration) =
            self.nodes(symbol.program_id).parent_kind(declaration)
        else {
            return None;
        };
        let imported_program_id = self
            .store
            .resolved_module(symbol.program_id, import_declaration.source.value.as_str())?;
        self.get_local_exported_symbol(imported_program_id, &imported_name)
    }

    fn get_local_exported_symbol(
        &self,
        program_id: ProgramId,
        export_name: &str,
    ) -> Option<SymbolRef> {
        let imported_entry = self.store.entry(program_id)?;
        let local_name = imported_entry
            .module_record()
            .local_export_entries
            .iter()
            .find_map(|entry| match &entry.export_name {
                ExportExportName::Name(name) if name.name == export_name => Some(&entry.local_name),
                ExportExportName::Default(_) if export_name == "default" => Some(&entry.local_name),
                _ => None,
            })?;
        let local_name = match local_name {
            ExportLocalName::Name(name) | ExportLocalName::Default(name) => name.name.as_str(),
            ExportLocalName::Null => return None,
        };
        let imported_symbol_id = imported_entry
            .semantic()
            .scoping()
            .get_root_binding(Ident::from(local_name))?;

        Some(SymbolRef::new(program_id, imported_symbol_id))
    }

    fn get_type_of_import_symbol(&self, symbol: SymbolRef) -> Option<Ty<'a>> {
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        let declaration_ref = NodeRef::new(symbol.program_id, declaration);
        if matches!(
            self.node_kind(declaration_ref),
            AstKind::ImportNamespaceSpecifier(_)
        ) {
            let AstKind::ImportDeclaration(import_declaration) =
                self.nodes(symbol.program_id).parent_kind(declaration)
            else {
                return None;
            };
            let imported_program_id = self
                .store
                .resolved_module(symbol.program_id, import_declaration.source.value.as_str())?;
            let namespace_name = self
                .semantic(symbol.program_id)
                .scoping()
                .symbol_name(symbol.symbol_id)
                .to_string();
            return Some(self.get_module_namespace_type(imported_program_id, &namespace_name));
        }

        let imported_symbol = self.get_imported_symbol(symbol)?;
        if let Some(alias_type) = self.get_type_of_imported_alias_symbol(imported_symbol) {
            return Some(alias_type);
        }

        Some(self.get_type_of_symbol(imported_symbol))
    }

    fn get_type_of_imported_alias_symbol(&self, symbol: SymbolRef) -> Option<Ty<'a>> {
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        let alias = match self.nodes(symbol.program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias) => alias,
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(symbol.program_id).parent_id(declaration);
                let AstKind::TSTypeAliasDeclaration(alias) =
                    self.nodes(symbol.program_id).kind(parent_id)
                else {
                    return None;
                };
                alias
            }
            _ => return None,
        };
        let ty = self.get_type_of_type_alias_declaration(symbol.program_id, alias);
        (!ty.is_none()).then_some(ty)
    }

    fn get_module_namespace_type(&self, program_id: ProgramId, namespace_name: &str) -> Ty<'a> {
        let Some(entry) = self.store.entry(program_id) else {
            return Ty::error(self.arena(), TypeErrorKind::UnresolvedImport);
        };
        let namespace_name = self.arena().str(namespace_name);
        let properties = entry
            .module_record()
            .local_export_entries
            .iter()
            .filter_map(|entry| {
                let property_name = match &entry.export_name {
                    ExportExportName::Name(name) => name.name.as_str(),
                    ExportExportName::Default(_) => "default",
                    ExportExportName::Null => return None,
                };
                let local_name = match &entry.local_name {
                    ExportLocalName::Name(name) | ExportLocalName::Default(name) => {
                        name.name.as_str()
                    }
                    ExportLocalName::Null if property_name == "default" => {
                        let declaration = self.nodes(program_id).iter().find_map(|node| {
                            let AstKind::ExportDefaultDeclaration(declaration) = node.kind() else {
                                return None;
                            };
                            (declaration.declaration.span() == entry.span).then_some(declaration)
                        })?;
                        let expression = declaration.declaration.as_expression()?;
                        let ty = self.get_type_of_expression_with_node(
                            program_id,
                            expression,
                            Some(declaration.node_id()),
                            GetTypeFlags::PRESERVE_LITERALS,
                        );
                        return Some(Ty::property(property_name, ty));
                    }
                    ExportLocalName::Null => return None,
                };
                let symbol = self.get_root_symbol(program_id, local_name)?;
                Some(Ty::property(property_name, self.get_type_of_symbol(symbol)))
            });
        Ty::module_namespace(self.arena(), namespace_name, properties)
    }

    fn get_type_of_array_expression(
        &self,
        program_id: ProgramId,
        array_expression: &'a ArrayExpression<'a>,
        node_id: Option<NodeId>,
        context: ExpressionCheckContext<'a>,
    ) -> Ty<'a> {
        if self.array_literal_context_produces_tuple(context) {
            let elements = array_expression
                .elements
                .iter()
                .enumerate()
                .map(|(index, element)| {
                    let contextual_element_type = self
                        .contextual_type_for_array_literal_element(context.contextual_type, index);
                    let element_context =
                        self.array_literal_element_context(context, contextual_element_type);
                    match element {
                        ArrayExpressionElement::SpreadElement(spread) => {
                            TupleElement::Rest(self.check_expression_with_context(
                                program_id,
                                AstKind::from_expression(&spread.argument),
                                node_id,
                                element_context,
                            ))
                        }
                        _ => TupleElement::Regular(self.get_type_of_array_expression_element(
                            program_id,
                            element,
                            node_id,
                            element_context,
                        )),
                    }
                })
                .collect();
            return if self.array_literal_context_produces_readonly_tuple(context) {
                Ty::readonly_tuple(self.arena(), elements)
            } else {
                Ty::tuple(self.arena(), elements)
            };
        }

        match array_expression.elements.len() {
            0 => Ty::array(
                self.arena(),
                evolving_arrays::empty_array_literal_element_type(
                    self,
                    program_id,
                    array_expression,
                    node_id,
                ),
            ),
            // For 1 element: infer the type of the first element
            1 => {
                let first_element = &array_expression.elements[0];
                let contextual_element_type =
                    self.contextual_type_for_array_literal_element(context.contextual_type, 0);
                let element_context =
                    self.array_literal_element_context(context, contextual_element_type);
                let element_type = self.get_type_of_array_expression_element(
                    program_id,
                    first_element,
                    node_id,
                    element_context,
                );
                Ty::array(self.arena(), element_type)
            }
            // For 2+ elements: try to create a union type if there are mixed types
            _ => {
                // TODO(perf): avoid allocating here somehow?
                let mut element_types = Vec::default();
                for (index, element) in array_expression.elements.iter().enumerate() {
                    let contextual_element_type = self
                        .contextual_type_for_array_literal_element(context.contextual_type, index);
                    let element_context =
                        self.array_literal_element_context(context, contextual_element_type);
                    let element_type = self.get_type_of_array_expression_element(
                        program_id,
                        element,
                        node_id,
                        element_context,
                    );
                    // TODO(perf): avoid re-iterating elements? use a hash set?
                    if !element_types
                        .iter()
                        .any(|existing| self.arena().is_type_identical_to(*existing, element_type))
                    {
                        element_types.push(element_type);
                    }
                }
                let element_type = if element_types.len() == 1 {
                    element_types[0]
                } else {
                    Ty::union(self.arena(), element_types)
                };
                Ty::array(self.arena(), element_type)
            }
        }
    }

    fn array_literal_context_produces_tuple(&self, context: ExpressionCheckContext<'a>) -> bool {
        context.check_mode.force_tuple()
            || context
                .contextual_type
                .is_some_and(|ty| matches!(self.arena().type_data(ty), TypeData::Tuple(_)))
    }

    fn array_literal_context_produces_readonly_tuple(
        &self,
        context: ExpressionCheckContext<'a>,
    ) -> bool {
        context.check_mode.const_context()
            || context.contextual_type.is_some_and(
                |ty| matches!(self.arena().type_data(ty), TypeData::Tuple(tuple) if tuple.readonly),
            )
    }

    fn contextual_type_for_array_literal_element(
        &self,
        contextual_type: Option<Ty<'a>>,
        index: usize,
    ) -> Option<Ty<'a>> {
        let contextual_type = contextual_type?;
        match self.arena().type_data(contextual_type) {
            TypeData::Tuple(tuple) => tuple.elements.get(index).map(TupleElement::ty),
            TypeData::Array(array) => Some(array.element_type),
            TypeData::Union(union) => {
                let element_types = union
                    .types
                    .iter()
                    .filter_map(|ty| {
                        self.contextual_type_for_array_literal_element(Some(*ty), index)
                    })
                    .collect::<Vec<_>>();
                (!element_types.is_empty()).then(|| Ty::union(self.arena(), element_types))
            }
            _ => None,
        }
    }

    fn array_literal_element_context(
        &self,
        context: ExpressionCheckContext<'a>,
        contextual_type: Option<Ty<'a>>,
    ) -> ExpressionCheckContext<'a> {
        let mut flags = context.flags | GetTypeFlags::CONTEXT_FREE;
        if !context.check_mode.const_context()
            && contextual_type.is_none_or(|ty| !type_contains_literal_type(self.arena(), ty, 0))
        {
            flags.remove(GetTypeFlags::PRESERVE_LITERALS);
        }
        ExpressionCheckContext {
            flags,
            contextual_type,
            check_mode: context.check_mode,
        }
    }

    fn get_type_of_array_expression_element(
        &self,
        program_id: ProgramId,
        element: &'a ArrayExpressionElement<'a>,
        node_id: Option<NodeId>,
        context: ExpressionCheckContext<'a>,
    ) -> Ty<'a> {
        let flags = context.flags;
        match element {
            ArrayExpressionElement::SpreadElement(spread) => {
                let argument_type = self.check_expression_with_context(
                    program_id,
                    AstKind::from_expression(&spread.argument),
                    node_id,
                    context,
                );
                let mut resolution_context = IterationResolutionContext::default();
                self.get_iteration_types_of_iterable(
                    program_id,
                    argument_type,
                    IterationResolverKind::Sync,
                    0,
                    &mut resolution_context,
                )
                .yield_type
                .or_else(|| argument_type.array_element_type(self.arena()))
                .or_else(|| {
                    argument_type
                        .is_any_like(self.arena())
                        .then_some(argument_type)
                })
                .unwrap_or_else(|| Ty::error(self.arena(), TypeErrorKind::UnsupportedType))
            }
            ArrayExpressionElement::Elision(_) => Ty::any(),
            _ => self.check_expression_with_context(
                program_id,
                AstKind::from_expression(element.to_expression()),
                node_id,
                context.with_flags(flags),
            ),
        }
    }

    fn get_type_of_function_declaration_group(
        &self,
        program_id: ProgramId,
        function: &'a Function<'a>,
        node_id: NodeId,
    ) -> Ty<'a> {
        let Some(identifier) = function.id.as_ref() else {
            return self.get_type_of_function_signature_with_node(
                program_id,
                FunctionKind::Function(function),
                Some(node_id),
            );
        };
        let function_name = identifier.name.as_str();
        let Some(symbol_id) = identifier.symbol_id.get() else {
            return self.get_type_of_function_signature_with_node(
                program_id,
                FunctionKind::Function(function),
                Some(node_id),
            );
        };

        let function_declarations = self.function_declarations_for_value_symbol(
            program_id,
            symbol_id,
            function_name,
            node_id,
        );

        let overload_declarations = function_declarations
            .iter()
            .copied()
            .filter(|(_, _, candidate)| candidate.body.is_none())
            .collect::<Vec<_>>();
        let callable_declarations = if overload_declarations.is_empty() {
            function_declarations
        } else {
            overload_declarations
        };

        if callable_declarations.len() <= 1 {
            let ty = self.get_type_of_function_signature_with_node(
                program_id,
                FunctionKind::Function(function),
                Some(node_id),
            );
            return self.add_expando_properties_to_callable_type(
                program_id,
                node_id,
                SymbolRef::new(program_id, symbol_id),
                ty,
            );
        }

        if self.has_class_declaration_named(program_id, function_name) {
            // TODO(overloads): TypeScript Go resolves class/function declaration conflicts through
            // binder symbol merging. Keep the class-side type for now instead of treating invalid
            // class/function collisions as callable overload groups.
            // TODO(correctness): model the class value-side as a real constructor object type
            // (`{ new(): Foo; prototype: Foo; …static members }`) instead of a `Ty::any` stub.
            return Ty::type_query(self.arena(), function_name, Ty::any(), std::iter::empty());
        }

        let signatures = callable_declarations.into_iter().map(
            |(declaration_program_id, declaration_id, declaration)| {
                let ty = self.get_type_of_function_signature_with_node(
                    declaration_program_id,
                    FunctionKind::Function(declaration),
                    Some(declaration_id),
                );
                let TypeData::Function(_) = self.arena().type_data(ty) else {
                    unreachable!("function declarations resolve to function types")
                };
                Signature::new(SignatureKind::Call, ty)
            },
        );
        let ty = Ty::object_with_signatures(self.arena(), [], signatures);
        self.add_expando_properties_to_callable_type(
            program_id,
            node_id,
            SymbolRef::new(program_id, symbol_id),
            ty,
        )
    }

    fn has_class_declaration_named(&self, program_id: ProgramId, name: &str) -> bool {
        self.semantic(program_id)
            .scoping()
            .get_root_binding(Ident::from(name))
            .is_some_and(|symbol_id| {
                self.get_class_for_symbol(SymbolRef::new(program_id, symbol_id))
                    .is_some()
            })
    }

    fn function_declarations_for_value_symbol(
        &self,
        program_id: ProgramId,
        symbol_id: SymbolId,
        function_name: &'a str,
        declaration_id: NodeId,
    ) -> Vec<(ProgramId, NodeId, &'a Function<'a>)> {
        let scoping = self.semantic(program_id).scoping();
        let is_root_function =
            scoping.get_root_binding(Ident::from(function_name)) == Some(symbol_id);

        if !self.is_global_script_entry(program_id)
            || self
                .store
                .entry(program_id)
                .is_some_and(program::ProgramEntry::is_lib)
        {
            return self.function_declarations_for_symbol(program_id, symbol_id);
        }

        let Some(namespace_path) = self.namespace_path_for_node(program_id, declaration_id) else {
            return self.function_declarations_for_symbol(program_id, symbol_id);
        };
        let mut seen = HashSet::new();
        let declarations = if is_root_function && namespace_path.is_empty() {
            self.store
                .entries()
                .iter()
                .filter(|entry| !entry.is_lib() && self.is_global_script_entry(entry.id()))
                .filter_map(|entry| {
                    entry
                        .semantic()
                        .scoping()
                        .get_root_binding(Ident::from(function_name))
                        .map(|symbol_id| (entry.id(), symbol_id))
                })
                .flat_map(|(program_id, symbol_id)| {
                    self.function_declarations_for_symbol(program_id, symbol_id)
                })
                .collect::<Vec<_>>()
        } else {
            self.store
                .entries()
                .iter()
                .filter(|entry| self.is_global_script_entry(entry.id()))
                .flat_map(|entry| {
                    self.function_declarations_for_namespace(
                        entry.id(),
                        &namespace_path,
                        function_name,
                    )
                })
                .collect::<Vec<_>>()
        };

        declarations
            .into_iter()
            .filter(|(program_id, declaration_id, _)| seen.insert((*program_id, *declaration_id)))
            .collect()
    }

    fn function_declarations_for_namespace(
        &self,
        program_id: ProgramId,
        namespace_path: &[&str],
        function_name: &str,
    ) -> Vec<(ProgramId, NodeId, &'a Function<'a>)> {
        let scoping = self.semantic(program_id).scoping();
        self.nodes(program_id)
            .iter_enumerated()
            .filter_map(|(node_id, node)| {
                let AstKind::TSModuleDeclaration(module) = node.kind() else {
                    return None;
                };
                let module_path = self.namespace_path_for_module(program_id, node_id)?;
                if module_path.as_slice() != namespace_path {
                    return None;
                }
                let scope_id = module.scope_id.get()?;
                let symbol_id = scoping.get_binding(scope_id, Ident::from(function_name))?;
                Some(self.function_declarations_for_symbol(program_id, symbol_id))
            })
            .flatten()
            .collect()
    }

    fn namespace_path_for_node(&self, program_id: ProgramId, node_id: NodeId) -> Option<Vec<&str>> {
        let mut path = Vec::new();
        for kind in self.nodes(program_id).ancestor_kinds(node_id) {
            match kind {
                AstKind::Program(_) => return Some(path),
                AstKind::TSModuleDeclaration(module) => {
                    let TSModuleDeclarationName::Identifier(identifier) = &module.id else {
                        return None;
                    };
                    path.push(identifier.name.as_str());
                }
                AstKind::TSModuleBlock(_) => {}
                _ => return None,
            }
        }
        None
    }

    fn namespace_path_for_module(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
    ) -> Option<Vec<&str>> {
        let AstKind::TSModuleDeclaration(module) = self.nodes(program_id).kind(node_id) else {
            return None;
        };
        let mut path = match &module.id {
            TSModuleDeclarationName::Identifier(identifier) => vec![identifier.name.as_str()],
            _ => return None,
        };
        path.extend(self.namespace_path_for_node(program_id, node_id)?);
        Some(path)
    }

    fn function_declarations_for_symbol(
        &self,
        program_id: ProgramId,
        symbol_id: SymbolId,
    ) -> Vec<(ProgramId, NodeId, &'a Function<'a>)> {
        // TypeScript overloads share a symbol. Use semantic declarations instead of scanning the
        // whole AST for same-name functions, which can also accidentally cross scope boundaries.
        self.semantic(program_id)
            .scoping()
            .symbol_declarations(symbol_id)
            .filter_map(
                |declaration_id| match self.nodes(program_id).kind(declaration_id) {
                    AstKind::Function(candidate) => Some((program_id, declaration_id, candidate)),
                    AstKind::BindingIdentifier(_) => {
                        let parent_id = self.nodes(program_id).parent_id(declaration_id);
                        match self.nodes(program_id).kind(parent_id) {
                            AstKind::Function(candidate) => {
                                Some((program_id, parent_id, candidate))
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                },
            )
            .collect()
    }

    fn is_global_script_entry(&self, program_id: ProgramId) -> bool {
        self.store.entry(program_id).is_some_and(|entry| {
            !entry.module_record().has_module_syntax
                && entry.module_record().requested_modules.is_empty()
                && entry.module_record().local_export_entries.is_empty()
        })
    }

    pub(crate) fn variable_declarator_for_symbol(
        &self,
        symbol: SymbolRef,
    ) -> Option<(NodeId, &'a VariableDeclarator<'a>)> {
        self.semantic(symbol.program_id)
            .scoping()
            .symbol_declarations(symbol.symbol_id)
            .find_map(|declaration| self.variable_declarator_at(symbol.program_id, declaration))
    }

    fn variable_declarator_at(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
    ) -> Option<(NodeId, &'a VariableDeclarator<'a>)> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::VariableDeclarator(declarator) => Some((declaration, declarator)),
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                match self.nodes(program_id).kind(parent_id) {
                    AstKind::VariableDeclarator(declarator) => Some((parent_id, declarator)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn simple_binding_symbol(
        &self,
        program_id: ProgramId,
        pattern: &BindingPattern<'a>,
    ) -> Option<SymbolRef> {
        match pattern {
            BindingPattern::BindingIdentifier(identifier) => identifier
                .symbol_id
                .get()
                .map(|symbol_id| SymbolRef::new(program_id, symbol_id)),
            _ => None,
        }
    }

    // Expando properties are members assigned onto a function object after the function is
    // declared, like `actionCreator.type = type`. TypeScript models the value as both callable
    // and object-like, so preserve the call signatures while adding the assigned properties.
    fn add_expando_properties_to_callable_type(
        &self,
        program_id: ProgramId,
        host_declaration: NodeId,
        host_symbol: SymbolRef,
        ty: Ty<'a>,
    ) -> Ty<'a> {
        let expando_properties =
            self.expando_properties_for_symbol(program_id, host_declaration, host_symbol);
        if expando_properties.is_empty() {
            return ty;
        }

        match self.arena().type_data(ty) {
            TypeData::Function(_) => Ty::object_with_signatures(
                self.arena(),
                expando_properties,
                [Signature::new(SignatureKind::Call, ty)],
            ),
            TypeData::Object(object) => self.arena().alloc_type(TypeData::Object(
                self.arena().alloc(TyObject {
                    properties: self
                        .arena()
                        .vec_from_iter(object.properties.iter().copied().chain(expando_properties)),
                    signatures: self
                        .arena()
                        .vec_from_iter(object.signatures.iter().copied()),
                    index_infos: self
                        .arena()
                        .vec_from_iter(object.index_infos.iter().copied()),
                    is_constructor_type: object.is_constructor_type,
                }),
            )),
            _ => ty,
        }
    }

    fn expando_properties_for_symbol(
        &self,
        program_id: ProgramId,
        host_declaration: NodeId,
        host_symbol: SymbolRef,
    ) -> Vec<TyProperty<'a>> {
        let Some(host_container_id) =
            self.enclosing_expando_container_id(program_id, host_declaration)
        else {
            return Vec::new();
        };

        let mut properties: Vec<TyProperty<'a>> = Vec::new();
        for node_id in self.expando_assignments_in_container(program_id, host_container_id) {
            let AstKind::AssignmentExpression(assignment) = self.nodes(program_id).kind(node_id)
            else {
                unreachable!("expando assignment index contains only assignment expressions")
            };
            let Some((name, right)) =
                self.static_property_assignment_for_symbol(program_id, assignment, host_symbol)
            else {
                continue;
            };
            let ty = self.get_type_of_expression_with_node(
                program_id,
                right,
                Some(assignment.node_id.get()),
                GetTypeFlags::NONE,
            );
            let method = ty.is_function(self.arena());
            if let Some(existing) = properties.iter_mut().find(|property| property.name == name) {
                existing.ty = ty;
                existing.method = method;
            } else {
                properties.push(TyProperty {
                    name,
                    ty,
                    computed: false,
                    optional: false,
                    method,
                    readonly: false,
                });
            }
        }
        properties
    }

    fn expando_assignments_in_container(
        &self,
        program_id: ProgramId,
        host_container_id: NodeId,
    ) -> Vec<NodeId> {
        if !self
            .expando_assignments_by_container
            .borrow()
            .contains_key(&program_id)
        {
            let mut assignments_by_container: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
            for (node_id, node) in self.nodes(program_id).iter_enumerated() {
                let AstKind::AssignmentExpression(assignment) = node.kind() else {
                    continue;
                };
                if assignment.operator != AssignmentOperator::Assign {
                    continue;
                }
                let Some(container_id) = self.enclosing_expando_container_id(program_id, node_id)
                else {
                    continue;
                };
                assignments_by_container
                    .entry(container_id)
                    .or_default()
                    .push(node_id);
            }
            self.expando_assignments_by_container
                .borrow_mut()
                .insert(program_id, assignments_by_container);
        }

        self.expando_assignments_by_container
            .borrow()
            .get(&program_id)
            .and_then(|assignments| assignments.get(&host_container_id))
            .cloned()
            .unwrap_or_default()
    }

    fn static_property_assignment_for_symbol(
        &self,
        program_id: ProgramId,
        assignment: &'a AssignmentExpression<'a>,
        host_symbol: SymbolRef,
    ) -> Option<(&'a str, &'a Expression<'a>)> {
        let AssignmentTarget::StaticMemberExpression(member) = &assignment.left else {
            return None;
        };
        let Expression::Identifier(identifier) = &member.object else {
            return None;
        };
        let object_symbol =
            self.get_symbol_at_location(self.identifier_node_ref(program_id, identifier))?;
        if object_symbol != host_symbol {
            return None;
        }
        Some((member.property.name.as_str(), &assignment.right))
    }

    fn enclosing_expando_container_id(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
    ) -> Option<NodeId> {
        self.nodes(program_id)
            .ancestors_enumerated(node_id)
            .find_map(|(ancestor_id, node)| match node.kind() {
                AstKind::Program(_)
                | AstKind::Function(_)
                | AstKind::ArrowFunctionExpression(_) => Some(ancestor_id),
                _ => None,
            })
    }

    fn get_type_of_variable_declarator(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        declarator: &'a VariableDeclarator<'a>,
    ) -> Ty<'a> {
        if declarator.type_annotation.is_some() {
            let ty = self.get_type_from_ts_type_annotation(
                program_id,
                declarator.type_annotation.as_deref(),
            );
            if matches!(self.arena().type_data(ty), TypeData::UniqueSymbol(symbol) if symbol.name.is_none())
                && let BindingPattern::BindingIdentifier(identifier) = &declarator.id
            {
                Ty::unique_symbol(self.arena(), Some(identifier.name.as_str()))
            } else {
                ty
            }
        } else {
            if let Some(ty) =
                self.get_type_of_for_statement_declarator(program_id, declaration, declarator)
            {
                return ty;
            }

            let Some(expression) = declarator.init.as_ref() else {
                return Ty::any();
            };
            let flags = if declarator.kind == VariableDeclarationKind::Const
                && !self.is_in_exported_declaration(program_id, declaration)
            {
                GetTypeFlags::PRESERVE_LITERALS
            } else {
                GetTypeFlags::NONE
            };
            let ty = self.get_type_of_expression_with_node(
                program_id,
                expression,
                Some(declaration),
                flags,
            );
            if declarator.kind != VariableDeclarationKind::Const
                && matches!(ty, Ty::Null | Ty::Undefined)
                && self.is_null_or_undefined_initializer(expression)
            {
                Ty::any()
            } else if expression.is_function() {
                self.simple_binding_symbol(program_id, &declarator.id)
                    .map_or(ty, |symbol| {
                        self.add_expando_properties_to_callable_type(
                            program_id,
                            declaration,
                            symbol,
                            ty,
                        )
                    })
            } else {
                ty
            }
        }
    }

    fn is_null_or_undefined_initializer(&self, expression: &Expression<'a>) -> bool {
        match expression {
            Expression::NullLiteral(_) => true,
            Expression::Identifier(identifier) => identifier.name == UNDEFINED_IDENT,
            Expression::UnaryExpression(unary) => unary.operator == UnaryOperator::Void,
            _ => false,
        }
    }

    fn get_type_of_for_statement_declarator(
        &self,
        program_id: ProgramId,
        declaration: NodeId,
        declarator: &'a VariableDeclarator<'a>,
    ) -> Option<Ty<'a>> {
        for (ancestor_id, node) in self.nodes(program_id).ancestors_enumerated(declaration) {
            match node.kind() {
                AstKind::ForInStatement(for_in)
                    if for_statement_left_contains_declarator(&for_in.left, declarator) =>
                {
                    let object_type = self.get_type_of_expression_with_node(
                        program_id,
                        &for_in.right,
                        Some(ancestor_id),
                        GetTypeFlags::NONE,
                    );
                    if self.is_scoped_type_parameter_reference(program_id, ancestor_id, object_type)
                    {
                        return Some(self.get_global_extract_type(
                            program_id,
                            Ty::keyof(self.arena(), object_type),
                            Ty::string(),
                        ));
                    }
                    return Some(Ty::string());
                }
                AstKind::ForOfStatement(for_of)
                    if for_statement_left_contains_declarator(&for_of.left, declarator) =>
                {
                    let iterable_type = self.get_type_of_expression_with_node(
                        program_id,
                        &for_of.right,
                        Some(ancestor_id),
                        GetTypeFlags::NONE,
                    );
                    return self.get_iteration_element_type(
                        program_id,
                        ancestor_id,
                        iterable_type,
                        for_of.r#await,
                    );
                }
                _ => {}
            }
        }
        None
    }

    fn get_type_of_binding_pattern(
        &self,
        program_id: ProgramId,
        declaration_node_id: NodeId,
        binding_pattern: BindingPatternKind<'a>,
        symbol_id: SymbolId,
    ) -> Option<Ty<'a>> {
        let (binding_type, binding_pattern) = match binding_pattern {
            BindingPatternKind::FormalParameter(parameter) => {
                let binding_type = parameter.type_annotation.as_deref().map_or_else(
                    || {
                        self.get_contextual_type_of_formal_parameter(
                            program_id,
                            declaration_node_id,
                            parameter,
                        )
                        .unwrap_or_else(Ty::any)
                    },
                    |annotation| {
                        self.get_declared_type_of_formal_parameter(
                            program_id, parameter, annotation,
                        )
                    },
                );
                (binding_type, &parameter.pattern)
            }
            BindingPatternKind::VariableDeclarator(declarator) => (
                self.get_type_of_variable_declarator(program_id, declaration_node_id, declarator),
                &declarator.id,
            ),
            BindingPatternKind::RestParameter(parameter) => (
                self.get_parameter_type_from_ts_type_annotation(
                    program_id,
                    parameter.type_annotation.as_deref(),
                ),
                &parameter.rest.argument,
            ),
        };
        self.get_type_of_binding_pattern_symbol(
            program_id,
            binding_pattern,
            symbol_id,
            binding_type,
        )
    }

    fn get_type_of_binding_identifier_from_binding_pattern(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        symbol_id: SymbolId,
    ) -> Option<Ty<'a>> {
        self.nodes(program_id)
            .ancestors_enumerated(node_id)
            .find_map(|(ancestor_id, ancestor)| match ancestor.kind() {
                // TODO: Change this to use a new `BindingPatternKind::from_kind` function so this is more generic
                AstKind::FormalParameter(parameter) => self.get_type_of_binding_pattern(
                    program_id,
                    ancestor_id,
                    BindingPatternKind::FormalParameter(parameter),
                    symbol_id,
                ),
                AstKind::FormalParameterRest(parameter) => self.get_type_of_binding_pattern(
                    program_id,
                    ancestor_id,
                    BindingPatternKind::RestParameter(parameter),
                    symbol_id,
                ),
                AstKind::VariableDeclarator(declarator) => self.get_type_of_binding_pattern(
                    program_id,
                    ancestor_id,
                    BindingPatternKind::VariableDeclarator(declarator),
                    symbol_id,
                ),
                _ => None,
            })
    }

    fn get_type_of_binding_pattern_symbol(
        &self,
        program_id: ProgramId,
        pattern: &BindingPattern<'a>,
        symbol_id: SymbolId,
        pattern_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        match pattern {
            BindingPattern::BindingIdentifier(identifier)
                if identifier.symbol_id.get() == Some(symbol_id) =>
            {
                Some(self.get_apparent_binding_type(program_id, pattern_type))
            }
            BindingPattern::BindingIdentifier(_) => None,
            BindingPattern::ObjectPattern(object) => {
                for property in &object.properties {
                    let Some(property_name) = property_key_name_str(&property.key) else {
                        continue;
                    };
                    let Some(property_type) = self.get_destructured_property_type(
                        program_id,
                        pattern_type,
                        property_name,
                    ) else {
                        continue;
                    };
                    if let Some(ty) = self.get_type_of_binding_pattern_symbol(
                        program_id,
                        &property.value,
                        symbol_id,
                        property_type,
                    ) {
                        return Some(ty);
                    }
                }

                object.rest.as_ref().and_then(|rest| {
                    self.get_type_of_binding_pattern_symbol(
                        program_id,
                        &rest.argument,
                        symbol_id,
                        Ty::any(),
                    )
                })
            }
            BindingPattern::ArrayPattern(array) => {
                for (index, element) in array.elements.iter().enumerate() {
                    let Some(element) = element else {
                        continue;
                    };
                    let element_type =
                        tuple_element_type_at_index(self.arena(), pattern_type, index)
                            .or_else(|| pattern_type.array_element_type(self.arena()))
                            .unwrap_or_else(Ty::any);
                    if let Some(ty) = self.get_type_of_binding_pattern_symbol(
                        program_id,
                        element,
                        symbol_id,
                        element_type,
                    ) {
                        return Some(ty);
                    }
                }

                array.rest.as_ref().and_then(|rest| {
                    self.get_type_of_binding_pattern_symbol(
                        program_id,
                        &rest.argument,
                        symbol_id,
                        pattern_type
                            .array_element_type(self.arena())
                            .map(|element_type| Ty::array(self.arena(), element_type))
                            .unwrap_or_else(Ty::any),
                    )
                })
            }
            BindingPattern::AssignmentPattern(assignment) => self
                .get_type_of_binding_pattern_symbol(
                    program_id,
                    &assignment.left,
                    symbol_id,
                    self.get_non_undefined_type(pattern_type),
                ),
        }
    }

    fn get_apparent_binding_type(&self, program_id: ProgramId, ty: Ty<'a>) -> Ty<'a> {
        self.get_apparent_type_at_use(program_id, ty, 0)
    }

    fn get_non_undefined_type(&self, ty: Ty<'a>) -> Ty<'a> {
        ty.map_union(self.arena(), |ty| (ty != Ty::Undefined).then_some(ty))
    }

    fn get_destructured_property_type(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        self.get_destructured_property_type_at_depth(program_id, object_type, property_name, 0)
    }

    fn get_destructured_property_type_at_depth(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return self.get_property_type_of_structural_type(
                program_id,
                object_type,
                property_name,
            );
        }

        match self.arena().type_data(object_type) {
            TypeData::Object(object) => object.properties.iter().find_map(|property| {
                if property.computed || property.name != property_name {
                    return None;
                }
                Some(if property.optional {
                    property.ty.or_undefined(self.arena())
                } else {
                    property.ty
                })
            }),
            TypeData::ModuleNamespace(namespace) => {
                namespace.properties.iter().find_map(|property| {
                    (property.name == property_name && !property.computed).then_some(property.ty)
                })
            }
            TypeData::Union(union) => {
                let property_types = union
                    .types
                    .iter()
                    .filter_map(|ty| {
                        self.get_destructured_property_type_at_depth(
                            program_id,
                            *ty,
                            property_name,
                            depth + 1,
                        )
                    })
                    .collect::<Vec<_>>();
                (!property_types.is_empty()).then(|| Ty::union(self.arena(), property_types))
            }
            TypeData::Intersection(intersection) => intersection.types.iter().find_map(|ty| {
                self.get_destructured_property_type_at_depth(
                    program_id,
                    *ty,
                    property_name,
                    depth + 1,
                )
            }),
            TypeData::TypeReference(reference) => self
                .get_property_type_of_structural_type(program_id, object_type, property_name)
                .or_else(|| {
                    self.get_expanded_type_alias_reference_type(program_id, object_type, depth + 1)
                        .and_then(|(expanded_program_id, expanded)| {
                            self.get_destructured_property_type_at_depth(
                                expanded_program_id,
                                expanded,
                                property_name,
                                depth + 1,
                            )
                        })
                })
                .or_else(|| {
                    self.get_property_type_of_interface_type(program_id, reference, property_name)
                }),
            _ => None,
        }
    }

    pub(crate) fn get_expanded_type_alias_reference_type(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Option<(ProgramId, Ty<'a>)> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }
        let TypeData::TypeReference(reference) = self.arena().type_data(ty) else {
            return None;
        };
        let (reference_program_id, alias_symbol, declaration) =
            if let Some(metadata) = self.type_alias_metadata(ty) {
                (
                    metadata.reference_program_id,
                    metadata.alias_symbol,
                    metadata.declaration,
                )
            } else {
                let (alias_symbol, declaration) =
                    self.get_type_symbol_and_declaration_for_name(program_id, reference.name)?;
                (
                    program_id,
                    alias_symbol,
                    NodeRef::new(alias_symbol.program_id, declaration),
                )
            };
        let type_arguments = if alias_symbol.program_id != reference_program_id {
            reference
                .type_arguments
                .iter()
                .map(|ty| {
                    self.expand_type_alias_argument_for_foreign_declaration(
                        reference_program_id,
                        *ty,
                        depth + 1,
                    )
                })
                .collect::<Vec<_>>()
        } else {
            reference.type_arguments.iter().copied().collect::<Vec<_>>()
        };
        self.get_expanded_type_alias_declaration(
            declaration.program_id,
            declaration.node_id,
            &type_arguments,
            depth + 1,
        )
        .map(|ty| (declaration.program_id, ty))
    }

    pub(crate) fn expand_type_alias_for_relation(
        &self,
        ty: Ty<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        let metadata = self.type_alias_metadata(ty)?;
        self.get_expanded_type_alias_reference_type(metadata.reference_program_id, ty, depth)
            .map(|(_, expanded)| expanded)
    }

    fn get_expanded_type_alias_reference_preserving_arguments(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Option<(ProgramId, Ty<'a>)> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }
        let TypeData::TypeReference(reference) = self.arena().type_data(ty) else {
            return None;
        };
        let declaration = if let Some(metadata) = self.type_alias_metadata(ty) {
            metadata.declaration
        } else {
            let (alias_symbol, declaration) =
                self.get_type_symbol_and_declaration_for_name(program_id, reference.name)?;
            NodeRef::new(alias_symbol.program_id, declaration)
        };
        self.get_expanded_type_alias_declaration(
            declaration.program_id,
            declaration.node_id,
            &reference.type_arguments,
            depth + 1,
        )
        .map(|ty| (declaration.program_id, ty))
    }

    fn get_declared_type_of_formal_parameter(
        &self,
        program_id: ProgramId,
        parameter: &'a FormalParameter<'a>,
        annotation: &'a TSTypeAnnotation<'a>,
    ) -> Ty<'a> {
        let annotated_type =
            self.get_parameter_type_from_ts_type_annotation(program_id, Some(annotation));
        let annotated_type = self.get_apparent_declared_parameter_type(program_id, annotated_type);
        let annotated_type = if let TypeData::Infer(infer) = self.arena().type_data(annotated_type)
        {
            Ty::type_reference(self.arena(), infer.type_parameter.name, [])
        } else {
            annotated_type
        };

        if parameter.optional {
            return annotated_type.or_undefined(self.arena());
        }

        annotated_type
    }

    fn get_type_of_binding_identifier_without_symbol(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
    ) -> Ty<'a> {
        let parent_id = self.nodes(program_id).parent_id(node_id);
        match self.nodes(program_id).kind(parent_id) {
            AstKind::FormalParameter(_) | AstKind::FormalParameterRest(_) => {
                self.get_type_at_location(NodeRef::new(program_id, parent_id))
            }
            _ => Ty::none(),
        }
    }

    fn get_type_of_type_predicate_identifier(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        name: &str,
    ) -> Ty<'a> {
        for ancestor in self.nodes(program_id).ancestor_kinds(node_id) {
            let parameters = match ancestor {
                AstKind::TSFunctionType(function) => {
                    self.function_signature_parameters(program_id, function.params.as_ref())
                }
                AstKind::TSMethodSignature(method) => {
                    self.function_signature_parameters(program_id, method.params.as_ref())
                }
                AstKind::TSCallSignatureDeclaration(signature) => {
                    self.function_signature_parameters(program_id, signature.params.as_ref())
                }
                AstKind::Function(function) => {
                    self.function_signature_parameters(program_id, &function.params)
                }
                AstKind::ArrowFunctionExpression(function) => {
                    self.function_signature_parameters(program_id, &function.params)
                }
                _ => continue,
            };
            if let Some(parameter) = parameters.iter().find(|parameter| parameter.name == name) {
                return parameter.ty;
            }
            return Ty::none();
        }
        Ty::none()
    }

    fn get_type_of_await_expression(
        &self,
        program_id: ProgramId,
        await_expr: &'a AwaitExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let ty = self.get_type_of_expression_with_node(
            program_id,
            &await_expr.argument,
            node_id,
            GetTypeFlags::PRESERVE_LITERALS,
        );
        self.get_awaited_type(program_id, ty)
    }

    fn get_type_of_yield_expression(
        &self,
        program_id: ProgramId,
        yield_expression: &'a YieldExpression<'a>,
    ) -> Ty<'a> {
        let Some(function) = self
            .nodes(program_id)
            .ancestors(yield_expression.node_id.get())
            .find_map(|node| match node.kind() {
                AstKind::Function(function) if function.generator => Some(function),
                _ => None,
            })
        else {
            return Ty::error(self.arena(), TypeErrorKind::UnsupportedType);
        };
        let resolver = if function.r#async {
            IterationResolverKind::Async
        } else {
            IterationResolverKind::Sync
        };

        if yield_expression.delegate {
            let Some(argument) = yield_expression.argument.as_ref() else {
                return Ty::error(self.arena(), TypeErrorKind::UnsupportedType);
            };
            let argument_type = self.get_type_of_expression_with_node(
                program_id,
                argument,
                None,
                GetTypeFlags::NONE,
            );
            let mut context = IterationResolutionContext::default();
            return self
                .get_iteration_types_of_iterable(
                    program_id,
                    argument_type,
                    resolver,
                    0,
                    &mut context,
                )
                .return_type
                .unwrap_or_else(Ty::undefined);
        }

        let Some(annotation) = function.return_type.as_deref() else {
            return Ty::any();
        };
        let return_type = self.get_type_from_ts_type_annotation(program_id, Some(annotation));
        let mut context = IterationResolutionContext::default();
        self.get_iteration_types_of_iterator(program_id, return_type, resolver, 0, &mut context)
            .next_type
            .unwrap_or_else(Ty::any)
    }

    fn get_awaited_type(&self, program_id: ProgramId, ty: Ty<'a>) -> Ty<'a> {
        match self.arena().type_data(ty) {
            TypeData::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.get_awaited_type(program_id, *ty)),
            ),
            TypeData::TypeReference(reference)
                if is_promise_like_type_reference(reference.name) =>
            {
                reference
                    .type_arguments
                    .first()
                    .copied()
                    .map(|ty| {
                        let awaited = self.get_awaited_type(program_id, ty);
                        self.expand_type_at_use(program_id, awaited, 0)
                    })
                    .unwrap_or(ty)
            }
            _ => self
                .get_structural_thenable_awaited_type(program_id, ty)
                .unwrap_or(ty),
        }
    }

    // TODO: Should we be looking at thenable specifically?
    fn get_structural_thenable_awaited_type(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
    ) -> Option<Ty<'a>> {
        let then_type = self.get_then_property_type(program_id, ty)?;
        let then_signatures =
            self.get_signatures_of_type_in_program(program_id, then_type, SignatureKind::Call);
        if then_signatures.is_empty() {
            return None;
        }

        let awaited_types = then_signatures
            .iter()
            .filter_map(|signature| signature.function(self.arena()).parameters.first())
            .flat_map(|parameter| self.get_fulfilled_value_types(program_id, parameter.ty))
            .map(|ty| {
                let awaited = self.get_awaited_type(program_id, ty);
                self.expand_type_at_use(program_id, awaited, 0)
            })
            .collect::<Vec<_>>();

        Some(if awaited_types.is_empty() {
            Ty::never()
        } else {
            Ty::union(self.arena(), awaited_types)
        })
    }

    fn get_then_property_type(&self, program_id: ProgramId, ty: Ty<'a>) -> Option<Ty<'a>> {
        match self.arena().type_data(ty) {
            TypeData::TypeReference(_) | TypeData::TypeQuery(_) => {
                self.get_property_type_of_named_type(program_id, &ty, "then")
            }
            _ => self.get_property_type_for_indexed_access(program_id, ty, "then"),
        }
    }

    fn get_fulfilled_value_types(
        &self,
        program_id: ProgramId,
        callback_type: Ty<'a>,
    ) -> Vec<Ty<'a>> {
        match self.arena().type_data(callback_type) {
            TypeData::Union(union) => union
                .types
                .iter()
                .filter(|ty| **ty != Ty::Null && **ty != Ty::Undefined && **ty != Ty::Never)
                .flat_map(|ty| self.get_fulfilled_value_types(program_id, *ty))
                .collect(),
            _ => self
                .get_signatures_of_type_in_program(program_id, callback_type, SignatureKind::Call)
                .iter()
                .filter_map(|signature| signature.function(self.arena()).parameters.first())
                .map(|parameter| parameter.ty)
                .collect(),
        }
    }

    fn resolved_property_key_name(
        &self,
        program_id: ProgramId,
        key: &'a PropertyKey<'a>,
    ) -> Option<&'a str> {
        property_key_name_str(key).or_else(|| {
            self.global_symbol_property_name(program_id, key)
                .map(|name| self.arena().str(&format!("Symbol.{name}")))
        })
    }

    fn global_symbol_property_name(
        &self,
        program_id: ProgramId,
        key: &'a PropertyKey<'a>,
    ) -> Option<&'a str> {
        let PropertyKey::StaticMemberExpression(member) = key else {
            return None;
        };
        let Expression::Identifier(identifier) = &member.object else {
            return None;
        };
        if identifier.name != "Symbol" {
            return None;
        }
        let symbol =
            self.get_symbol_at_location(self.identifier_node_ref(program_id, identifier))?;
        if !self
            .store
            .entry(symbol.program_id)
            .is_some_and(program::ProgramEntry::is_lib)
        {
            return None;
        }
        Some(member.property.name.as_str())
    }

    fn well_known_symbol_property_name(
        &self,
        program_id: ProgramId,
        key: &'a PropertyKey<'a>,
    ) -> Option<&'static str> {
        match self.global_symbol_property_name(program_id, key)? {
            "iterator" => Some(SYMBOL_ITERATOR_PROPERTY_NAME),
            "asyncIterator" => Some(SYMBOL_ASYNC_ITERATOR_PROPERTY_NAME),
            _ => None,
        }
    }

    fn get_iteration_element_type(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        iterable_type: Ty<'a>,
        is_await: bool,
    ) -> Option<Ty<'a>> {
        let mut context = IterationResolutionContext::default();
        let mut iteration_types = if is_await {
            let async_types = self.get_iteration_types_of_iterable(
                program_id,
                iterable_type,
                IterationResolverKind::Async,
                0,
                &mut context,
            );
            if async_types.has_types() {
                async_types
            } else {
                self.get_iteration_types_of_iterable(
                    program_id,
                    iterable_type,
                    IterationResolverKind::Sync,
                    0,
                    &mut context,
                )
            }
        } else {
            self.get_iteration_types_of_iterable(
                program_id,
                iterable_type,
                IterationResolverKind::Sync,
                0,
                &mut context,
            )
        };

        if is_await {
            iteration_types.yield_type = iteration_types
                .yield_type
                .map(|ty| self.get_for_of_element_type(program_id, node_id, ty, true));
            iteration_types.return_type = iteration_types
                .return_type
                .map(|ty| self.get_for_of_element_type(program_id, node_id, ty, true));
        }
        iteration_types.yield_type
    }

    pub(crate) fn get_inference_argument_type(
        &self,
        program_id: ProgramId,
        parameter_type: Ty<'a>,
        argument_type: Ty<'a>,
    ) -> Ty<'a> {
        let TypeData::TypeReference(reference) = self.arena().type_data(parameter_type) else {
            return argument_type;
        };

        let global_iterable_type_ref = self.get_global_iterable_type(program_id, Ty::any());
        let TypeData::TypeReference(global_iterable_reference) =
            self.arena().type_data(global_iterable_type_ref)
        else {
            return argument_type;
        };

        if global_iterable_reference.name != reference.name
            || !self.is_lib_type_reference(program_id, reference)
        {
            return argument_type;
        }

        let mut context = IterationResolutionContext::default();
        let iteration_types = self.get_iteration_types_of_iterable(
            program_id,
            argument_type,
            IterationResolverKind::Sync,
            0,
            &mut context,
        );
        let Some(element_type) = iteration_types.yield_type else {
            return argument_type;
        };

        Ty::type_reference(self.arena(), reference.name, [element_type])
    }

    fn get_iteration_types_of_iterable(
        &self,
        program_id: ProgramId,
        iterable_type: Ty<'a>,
        resolver: IterationResolverKind,
        depth: usize,
        context: &mut IterationResolutionContext,
    ) -> IterationTypes<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return IterationTypes::default();
        }

        match self.arena().type_data(iterable_type) {
            TypeData::Any => IterationTypes {
                yield_type: Some(Ty::any()),
                return_type: Some(Ty::any()),
                next_type: Some(Ty::any()),
            },
            TypeData::Error(_) => IterationTypes {
                yield_type: Some(iterable_type),
                return_type: Some(iterable_type),
                next_type: Some(iterable_type),
            },
            TypeData::Union(union) => self.combine_iteration_types(union.types.iter().map(|ty| {
                self.get_iteration_types_of_iterable(program_id, *ty, resolver, depth + 1, context)
            })),
            TypeData::Array(array) if resolver == IterationResolverKind::Sync => IterationTypes {
                yield_type: Some(array.element_type),
                ..IterationTypes::default()
            },
            TypeData::Tuple(tuple) if resolver == IterationResolverKind::Sync => IterationTypes {
                yield_type: Some(Ty::union(
                    self.arena(),
                    tuple.elements.iter().map(|element| element.ty()),
                )),
                ..IterationTypes::default()
            },
            TypeData::String | TypeData::StringLiteral(_) | TypeData::TemplateLiteral(_)
                if resolver == IterationResolverKind::Sync =>
            {
                IterationTypes {
                    yield_type: Some(Ty::string()),
                    ..IterationTypes::default()
                }
            }
            TypeData::TypeReference(reference) => {
                let fast =
                    self.get_global_iteration_types_fast(program_id, reference, resolver, true);
                if fast.has_types() {
                    fast
                } else {
                    self.get_iteration_types_of_iterable_slow(
                        program_id,
                        iterable_type,
                        resolver,
                        depth + 1,
                        context,
                    )
                }
            }
            _ => self.get_iteration_types_of_iterable_slow(
                program_id,
                iterable_type,
                resolver,
                depth + 1,
                context,
            ),
        }
    }

    fn get_global_iteration_types_fast(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
        resolver: IterationResolverKind,
        require_iterable: bool,
    ) -> IterationTypes<'a> {
        if !self.is_lib_type_name(program_id, reference.name) {
            return IterationTypes::default();
        }

        // TypeScript keeps this direct-target path as an optimization before
        // falling back to the structural iteration protocol below.
        let is_iteration_family = match (resolver, require_iterable) {
            (IterationResolverKind::Sync, true) => matches!(
                reference.name,
                "Iterable" | "IterableIterator" | "IteratorObject" | "Generator"
            ),
            (IterationResolverKind::Sync, false) => matches!(
                reference.name,
                "Iterator" | "IterableIterator" | "IteratorObject" | "Generator"
            ),
            (IterationResolverKind::Async, true) => matches!(
                reference.name,
                "AsyncIterable"
                    | "AsyncIterableIterator"
                    | "AsyncIteratorObject"
                    | "AsyncGenerator"
            ),
            (IterationResolverKind::Async, false) => matches!(
                reference.name,
                "AsyncIterator"
                    | "AsyncIterableIterator"
                    | "AsyncIteratorObject"
                    | "AsyncGenerator"
            ),
        };
        let is_builtin_iterator = matches!(
            (resolver, reference.name),
            (
                IterationResolverKind::Sync,
                "ArrayIterator" | "MapIterator" | "SetIterator" | "StringIterator"
            ) | (IterationResolverKind::Async, "ReadableStreamAsyncIterator")
        );
        if !is_iteration_family && !is_builtin_iterator {
            return IterationTypes::default();
        }

        IterationTypes {
            yield_type: reference.type_arguments.first().copied(),
            return_type: reference.type_arguments.get(1).copied(),
            next_type: reference.type_arguments.get(2).copied(),
        }
    }

    fn get_iteration_types_of_iterable_slow(
        &self,
        program_id: ProgramId,
        iterable_type: Ty<'a>,
        resolver: IterationResolverKind,
        depth: usize,
        context: &mut IterationResolutionContext,
    ) -> IterationTypes<'a> {
        let Some(method_type) = self.get_well_known_symbol_property_type(
            program_id,
            iterable_type,
            resolver,
            depth + 1,
            context,
        ) else {
            return IterationTypes::default();
        };

        let iteration_types = self
            .get_signatures_of_type_in_program(program_id, method_type, SignatureKind::Call)
            .into_iter()
            .filter(|signature| {
                function_minimum_argument_count(self.arena(), signature.function(self.arena())) == 0
            })
            .map(|signature| {
                self.get_iteration_types_of_iterator(
                    program_id,
                    signature.function(self.arena()).return_type,
                    resolver,
                    depth + 1,
                    context,
                )
            });
        self.combine_iteration_types(iteration_types)
    }

    fn get_iteration_types_of_iterator(
        &self,
        program_id: ProgramId,
        iterator_type: Ty<'a>,
        resolver: IterationResolverKind,
        depth: usize,
        context: &mut IterationResolutionContext,
    ) -> IterationTypes<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return IterationTypes::default();
        }
        if let TypeData::TypeReference(reference) = self.arena().type_data(iterator_type) {
            let fast = self.get_global_iteration_types_fast(program_id, reference, resolver, false);
            if fast.has_types() {
                return fast;
            }
        }

        let active_interface =
            if let TypeData::TypeReference(reference) = self.arena().type_data(iterator_type) {
                self.get_type_symbol_and_declaration_for_name(program_id, reference.name)
                    .map(|(symbol, _)| {
                        IterationInterfaceResolution::new(
                            IterationInterfaceResolutionKind::Iterator,
                            resolver,
                            symbol,
                            reference,
                        )
                    })
            } else {
                None
            };
        if let Some(active_interface) = &active_interface
            && !context.active_interfaces.insert(active_interface.clone())
        {
            return IterationTypes::default();
        }

        let iteration_types = self.get_iteration_types_of_iterator_worker(
            program_id,
            iterator_type,
            resolver,
            depth,
            context,
        );
        if let Some(active_interface) = &active_interface {
            context.active_interfaces.remove(active_interface);
        }
        iteration_types
    }

    fn get_iteration_types_of_iterator_worker(
        &self,
        program_id: ProgramId,
        iterator_type: Ty<'a>,
        resolver: IterationResolverKind,
        depth: usize,
        context: &mut IterationResolutionContext,
    ) -> IterationTypes<'a> {
        let Some(next_type) =
            self.get_property_type_for_indexed_access(program_id, iterator_type, "next")
        else {
            let TypeData::TypeReference(reference) = self.arena().type_data(iterator_type) else {
                return IterationTypes::default();
            };
            return self.combine_iteration_types(
                self.get_interface_heritage_types(program_id, reference)
                    .into_iter()
                    .map(|(heritage_program_id, heritage_type)| {
                        self.get_iteration_types_of_iterator(
                            heritage_program_id,
                            heritage_type,
                            resolver,
                            depth + 1,
                            context,
                        )
                    }),
            );
        };
        let mut next_types = Vec::new();
        let mut result_types = Vec::new();
        for signature in
            self.get_signatures_of_type_in_program(program_id, next_type, SignatureKind::Call)
        {
            if let Some(next_type) = function_parameter_type_at_call_index(
                self.arena(),
                signature.function(self.arena()),
                0,
            ) {
                next_types.push(next_type);
            }
            let mut result_type = signature.function(self.arena()).return_type;
            if resolver == IterationResolverKind::Async {
                result_type = self.get_awaited_type(program_id, result_type);
            }
            result_types.push(self.get_iteration_types_of_iterator_result(
                program_id,
                result_type,
                depth + 1,
            ));
        }
        let mut iteration_types = self.combine_iteration_types(result_types);
        iteration_types.next_type = Some(if next_types.is_empty() {
            Ty::unknown()
        } else {
            Ty::union(self.arena(), next_types)
        });
        iteration_types
    }

    fn get_iteration_types_of_iterator_result(
        &self,
        program_id: ProgramId,
        result_type: Ty<'a>,
        depth: usize,
    ) -> IterationTypes<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return IterationTypes::default();
        }
        match self.arena().type_data(result_type) {
            TypeData::Any => IterationTypes {
                yield_type: Some(Ty::any()),
                return_type: Some(Ty::any()),
                next_type: None,
            },
            TypeData::Error(_) => IterationTypes {
                yield_type: Some(result_type),
                return_type: Some(result_type),
                next_type: None,
            },
            TypeData::Union(union) => {
                self.combine_iteration_types(union.types.iter().map(|ty| {
                    self.get_iteration_types_of_iterator_result(program_id, *ty, depth + 1)
                }))
            }
            TypeData::TypeReference(reference)
                if self.is_lib_type_name(program_id, reference.name)
                    && reference.name == "IteratorYieldResult" =>
            {
                IterationTypes {
                    yield_type: reference.type_arguments.first().copied(),
                    ..IterationTypes::default()
                }
            }
            TypeData::TypeReference(reference)
                if self.is_lib_type_name(program_id, reference.name)
                    && reference.name == "IteratorReturnResult" =>
            {
                IterationTypes {
                    return_type: reference.type_arguments.first().copied(),
                    ..IterationTypes::default()
                }
            }
            TypeData::TypeReference(_) => {
                if let Some((expanded_program_id, expanded)) =
                    self.get_expanded_type_alias_reference_type(program_id, result_type, depth + 1)
                    && expanded != result_type
                {
                    return self.get_iteration_types_of_iterator_result(
                        expanded_program_id,
                        expanded,
                        depth + 1,
                    );
                }
                self.get_structural_iteration_types_of_iterator_result(program_id, result_type)
            }
            TypeData::Object(_) | TypeData::Intersection(_) => {
                self.get_structural_iteration_types_of_iterator_result(program_id, result_type)
            }
            _ => IterationTypes::default(),
        }
    }

    fn get_structural_iteration_types_of_iterator_result(
        &self,
        program_id: ProgramId,
        result_type: Ty<'a>,
    ) -> IterationTypes<'a> {
        let done_type = self.get_property_type_for_indexed_access(program_id, result_type, "done");
        let value_type = self
            .get_property_type_for_indexed_access(program_id, result_type, "value")
            .unwrap_or_else(Ty::any);
        let states = done_type.map_or(
            IteratorResultStates {
                can_yield: true,
                can_return: false,
            },
            |done_type| self.iterator_result_done_states(done_type),
        );
        IterationTypes {
            yield_type: states.can_yield.then_some(value_type),
            return_type: states.can_return.then_some(value_type),
            next_type: None,
        }
    }

    fn iterator_result_done_states(&self, done_type: Ty<'a>) -> IteratorResultStates {
        match self.arena().type_data(done_type) {
            TypeData::BooleanLiteral(false) | TypeData::Undefined => IteratorResultStates {
                can_yield: true,
                can_return: false,
            },
            TypeData::BooleanLiteral(true) => IteratorResultStates {
                can_yield: false,
                can_return: true,
            },
            TypeData::Union(union) => union.types.iter().fold(
                IteratorResultStates {
                    can_yield: false,
                    can_return: false,
                },
                |states, ty| states.union(self.iterator_result_done_states(*ty)),
            ),
            TypeData::Never => IteratorResultStates {
                can_yield: false,
                can_return: false,
            },
            _ => IteratorResultStates {
                can_yield: true,
                can_return: true,
            },
        }
    }

    fn combine_iteration_types(
        &self,
        iteration_types: impl IntoIterator<Item = IterationTypes<'a>>,
    ) -> IterationTypes<'a> {
        let mut yield_types = Vec::new();
        let mut return_types = Vec::new();
        let mut next_types = Vec::new();
        for iteration_types in iteration_types {
            yield_types.extend(iteration_types.yield_type);
            return_types.extend(iteration_types.return_type);
            next_types.extend(iteration_types.next_type);
        }
        let combine =
            |types: Vec<Ty<'a>>| (!types.is_empty()).then(|| Ty::union(self.arena(), types));
        IterationTypes {
            yield_type: combine(yield_types),
            return_type: combine(return_types),
            next_type: combine(next_types),
        }
    }

    fn get_well_known_symbol_property_type(
        &self,
        program_id: ProgramId,
        object_type: Ty<'a>,
        resolver: IterationResolverKind,
        depth: usize,
        context: &mut IterationResolutionContext,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }
        match self.arena().type_data(object_type) {
            TypeData::Object(object) => object.properties.iter().find_map(|property| {
                (property.computed && property.name == resolver.property_name())
                    .then_some(property.ty)
            }),
            TypeData::Union(union) => {
                let property_types = union
                    .types
                    .iter()
                    .map(|ty| {
                        self.get_well_known_symbol_property_type(
                            program_id,
                            *ty,
                            resolver,
                            depth + 1,
                            context,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(Ty::union(self.arena(), property_types))
            }
            TypeData::Intersection(intersection) => intersection.types.iter().find_map(|ty| {
                self.get_well_known_symbol_property_type(
                    program_id,
                    *ty,
                    resolver,
                    depth + 1,
                    context,
                )
            }),
            TypeData::TypeReference(reference) => self
                .get_expanded_type_alias_reference_type(program_id, object_type, depth + 1)
                .and_then(|(expanded_program_id, expanded)| {
                    (expanded != object_type).then(|| {
                        self.get_well_known_symbol_property_type(
                            expanded_program_id,
                            expanded,
                            resolver,
                            depth + 1,
                            context,
                        )
                    })
                })
                .flatten()
                .or_else(|| {
                    self.get_well_known_symbol_property_type_of_interface(
                        program_id,
                        reference,
                        resolver,
                        depth + 1,
                        context,
                    )
                }),
            _ => None,
        }
    }

    fn get_well_known_symbol_property_type_of_interface(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
        resolver: IterationResolverKind,
        depth: usize,
        context: &mut IterationResolutionContext,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }
        let (symbol, _) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)?;
        let active_interface = IterationInterfaceResolution::new(
            IterationInterfaceResolutionKind::IterableProperty,
            resolver,
            symbol,
            reference,
        );
        if !context.active_interfaces.insert(active_interface.clone()) {
            return None;
        }
        let property_type = self.get_well_known_symbol_property_type_of_interface_worker(
            program_id, reference, resolver, depth, context,
        );
        context.active_interfaces.remove(&active_interface);
        property_type
    }

    fn get_well_known_symbol_property_type_of_interface_worker(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
        resolver: IterationResolverKind,
        depth: usize,
        context: &mut IterationResolutionContext,
    ) -> Option<Ty<'a>> {
        let declarations = self.interface_declarations_for_type_name(program_id, reference.name);

        let mut method_signatures = Vec::new();
        for &(interface_program_id, interface) in &declarations {
            let mapper = self
                .type_parameter_substitutions_for_reference(
                    interface_program_id,
                    interface.type_parameters.as_deref(),
                    reference,
                )
                .to_mapper(self.arena());
            for signature in &interface.body.body {
                match signature {
                    TSSignature::TSPropertySignature(property)
                        if !property.optional
                            && self.well_known_symbol_property_name(
                                interface_program_id,
                                &property.key,
                            ) == Some(resolver.property_name()) =>
                    {
                        let ty = self.get_type_from_ts_type_annotation(
                            interface_program_id,
                            property.type_annotation.as_deref(),
                        );
                        return Some(self.instantiate_type(ty, &mapper));
                    }
                    TSSignature::TSMethodSignature(method)
                        if !method.optional
                            && method.kind == TSMethodSignatureKind::Method
                            && self.well_known_symbol_property_name(
                                interface_program_id,
                                &method.key,
                            ) == Some(resolver.property_name()) =>
                    {
                        let signature =
                            self.signature_from_ts_method_signature(interface_program_id, method);
                        method_signatures.push(self.instantiate_signature(signature, &mapper));
                    }
                    _ => {}
                }
            }
        }
        if !method_signatures.is_empty() {
            return Some(match method_signatures.as_slice() {
                [signature] => signature.ty,
                _ => Ty::object_with_signatures(self.arena(), [], method_signatures),
            });
        }

        for (heritage_program_id, heritage_type) in
            self.get_interface_heritage_types(program_id, reference)
        {
            if let Some(property_type) = self.get_well_known_symbol_property_type(
                heritage_program_id,
                heritage_type,
                resolver,
                depth + 1,
                context,
            ) {
                return Some(property_type);
            }
        }
        None
    }

    fn get_interface_heritage_types(
        &self,
        program_id: ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> Vec<(ProgramId, Ty<'a>)> {
        let Some((symbol, _)) =
            self.get_type_symbol_and_declaration_for_name(program_id, reference.name)
        else {
            return Vec::new();
        };
        self.interface_declarations_for_symbol(symbol)
            .into_iter()
            .flat_map(|interface| {
                let mapper = self
                    .type_parameter_substitutions_for_reference(
                        symbol.program_id,
                        interface.type_parameters.as_deref(),
                        reference,
                    )
                    .to_mapper(self.arena());
                interface.extends.iter().filter_map(move |heritage| {
                    let Expression::Identifier(identifier) = &heritage.expression else {
                        return None;
                    };
                    let mut type_arguments = heritage
                        .type_arguments
                        .as_ref()
                        .into_iter()
                        .flat_map(|arguments| arguments.params.iter())
                        .map(|ty| {
                            self.instantiate_type(
                                self.get_type_argument_from_ts_type(symbol.program_id, ty),
                                &mapper,
                            )
                        })
                        .collect::<Vec<_>>();
                    self.fill_default_type_arguments(
                        symbol.program_id,
                        identifier.name.as_str(),
                        &mut type_arguments,
                    );
                    Some((
                        symbol.program_id,
                        Ty::type_reference(self.arena(), identifier.name.as_str(), type_arguments),
                    ))
                })
            })
            .collect()
    }

    fn interface_declarations_for_symbol(
        &self,
        symbol: SymbolRef,
    ) -> Vec<&'a TSInterfaceDeclaration<'a>> {
        self.semantic(symbol.program_id)
            .scoping()
            .symbol_declarations(symbol.symbol_id)
            .filter_map(
                |declaration| match self.nodes(symbol.program_id).kind(declaration) {
                    AstKind::TSInterfaceDeclaration(interface) => Some(interface),
                    AstKind::BindingIdentifier(_) => {
                        let parent = self.nodes(symbol.program_id).parent_id(declaration);
                        match self.nodes(symbol.program_id).kind(parent) {
                            AstKind::TSInterfaceDeclaration(interface) => Some(interface),
                            _ => None,
                        }
                    }
                    _ => None,
                },
            )
            .collect()
    }

    fn get_for_of_element_type(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        element_type: Ty<'a>,
        is_await: bool,
    ) -> Ty<'a> {
        if !is_await {
            return element_type;
        }
        let awaited_type = self.get_awaited_type(program_id, element_type);
        if awaited_type != element_type {
            return awaited_type;
        }
        if self.is_scoped_type_parameter_reference(program_id, node_id, element_type) {
            return self.get_global_awaited_type(program_id, element_type);
        }
        element_type
    }

    pub(crate) fn get_type_parameter_constraint(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        ty: Ty<'a>,
    ) -> Option<Ty<'a>> {
        let TypeData::TypeReference(reference) = self.arena().type_data(ty) else {
            return None;
        };
        if !reference.is_bare() {
            return None;
        }

        let current_type_parameters = match self.nodes(program_id).kind(node_id) {
            AstKind::Function(function) => function.type_parameters.as_deref(),
            AstKind::ArrowFunctionExpression(function) => function.type_parameters.as_deref(),
            AstKind::Class(class) => class.type_parameters.as_deref(),
            AstKind::TSInterfaceDeclaration(interface) => interface.type_parameters.as_deref(),
            AstKind::TSTypeAliasDeclaration(alias) => alias.type_parameters.as_deref(),
            _ => None,
        };
        if let Some(parameter) = current_type_parameters.and_then(|parameters| {
            parameters
                .params
                .iter()
                .find(|parameter| parameter.name.name == reference.name)
        }) {
            return parameter
                .constraint
                .as_ref()
                .map(|constraint| self.get_type_from_ts_type(program_id, constraint));
        }

        for ancestor in self.nodes(program_id).ancestors(node_id) {
            let type_parameters = match ancestor.kind() {
                AstKind::Function(function) => function.type_parameters.as_deref(),
                AstKind::ArrowFunctionExpression(function) => function.type_parameters.as_deref(),
                AstKind::Class(class) => class.type_parameters.as_deref(),
                AstKind::TSInterfaceDeclaration(interface) => interface.type_parameters.as_deref(),
                AstKind::TSTypeAliasDeclaration(alias) => alias.type_parameters.as_deref(),
                _ => continue,
            };
            let Some(parameter) = type_parameters.and_then(|parameters| {
                parameters
                    .params
                    .iter()
                    .find(|parameter| parameter.name.name == reference.name)
            }) else {
                continue;
            };
            return parameter
                .constraint
                .as_ref()
                .map(|constraint| self.get_type_from_ts_type(program_id, constraint));
        }

        None
    }

    pub(crate) fn is_scoped_type_parameter_reference(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
        ty: Ty<'a>,
    ) -> bool {
        let TypeData::TypeReference(reference) = self.arena().type_data(ty) else {
            return false;
        };
        if !reference.is_bare() {
            return false;
        }
        self.type_parameter_names_in_scope(program_id, node_id)
            .contains(&reference.name)
    }

    fn type_parameter_names_in_scope(
        &self,
        program_id: ProgramId,
        node_id: NodeId,
    ) -> Vec<&'a str> {
        let mut names = Vec::new();
        match self.nodes(program_id).kind(node_id) {
            AstKind::Function(function) => {
                push_type_parameter_names(&mut names, function.type_parameters.as_deref());
            }
            AstKind::ArrowFunctionExpression(function) => {
                push_type_parameter_names(&mut names, function.type_parameters.as_deref());
            }
            AstKind::Class(class) => {
                push_type_parameter_names(&mut names, class.type_parameters.as_deref());
            }
            AstKind::TSInterfaceDeclaration(interface) => {
                push_type_parameter_names(&mut names, interface.type_parameters.as_deref());
            }
            AstKind::TSTypeAliasDeclaration(alias) => {
                push_type_parameter_names(&mut names, alias.type_parameters.as_deref());
            }
            _ => {}
        }
        for ancestor in self.nodes(program_id).ancestors(node_id) {
            match ancestor.kind() {
                AstKind::Function(function) => {
                    push_type_parameter_names(&mut names, function.type_parameters.as_deref());
                }
                AstKind::ArrowFunctionExpression(function) => {
                    push_type_parameter_names(&mut names, function.type_parameters.as_deref());
                }
                AstKind::Class(class) => {
                    push_type_parameter_names(&mut names, class.type_parameters.as_deref());
                }
                AstKind::TSInterfaceDeclaration(interface) => {
                    push_type_parameter_names(&mut names, interface.type_parameters.as_deref());
                }
                AstKind::TSTypeAliasDeclaration(alias) => {
                    push_type_parameter_names(&mut names, alias.type_parameters.as_deref());
                }
                _ => {}
            }
        }
        names
    }

    fn is_in_chain_expression(&self, program_id: ProgramId, node_id: Option<NodeId>) -> bool {
        if let Some(node_id) = node_id {
            matches!(
                self.semantic(program_id).nodes().parent_kind(node_id),
                AstKind::ChainExpression(_)
            )
        } else {
            false
        }
    }

    fn resolve_imported_type_alias_symbol(&self, symbol: SymbolRef) -> Option<SymbolRef> {
        let mut current = self.get_imported_symbol(symbol)?;
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(current) {
                return None;
            }
            let declaration = self
                .semantic(current.program_id)
                .scoping()
                .symbol_declaration(current.symbol_id);
            if self
                .type_alias_declaration_node(current.program_id, declaration)
                .is_some()
            {
                return Some(current);
            }
            current = self.get_imported_symbol(current)?;
        }
    }

    fn is_type_alias_display_location(&self, location: NodeRef) -> bool {
        if matches!(
            self.node_kind(location),
            AstKind::BindingIdentifier(_)
                if matches!(
                    self.nodes(location.program_id)
                        .parent_kind(location.node_id),
                    AstKind::TSTypeAliasDeclaration(_)
                )
        ) {
            return true;
        }

        let symbol = match self.node_kind(location) {
            AstKind::BindingIdentifier(_) | AstKind::IdentifierReference(_) => {
                self.get_symbol_at_location(location)
            }
            AstKind::ExportSpecifier(specifier) => specifier
                .local
                .identifier_name()
                .and_then(|name| self.get_root_symbol(location.program_id, name.as_str())),
            _ => None,
        };
        let Some(symbol) = symbol else {
            return false;
        };
        self.resolve_imported_type_alias_symbol(symbol).is_some()
    }

    fn type_string_context_at_location(&self, location: NodeRef) -> TypeStringContext {
        let in_type_alias = self.is_type_alias_display_location(location);
        TypeStringContext {
            in_type_alias,
            expand_transparent_aliases: self.location_expands_transparent_type_aliases(location),
            expand_named_alias_chains: self.location_expands_named_type_alias_chains(location),
        }
    }

    fn type_to_string_with_context(&self, t: Ty<'a>, context: TypeStringContext) -> String {
        let cache_key = TypeStringCacheKey { ty: t, context };
        if let Some(cached) = self.type_string_cache.borrow().get(&cache_key) {
            return cached.clone();
        }
        let alias_chain_replacements = self.type_alias_chain_display_replacements(t, context);
        let type_string = t.to_type_string_with_depth(
            self.arena(),
            &|ty| {
                alias_chain_replacements
                    .get(&ty)
                    .copied()
                    .or_else(|| self.transparent_type_alias_target(ty, context))
            },
            &self.type_string_depth,
        );
        self.type_string_cache
            .borrow_mut()
            .insert(cache_key, type_string.clone());
        type_string
    }

    fn location_expands_transparent_type_aliases(&self, location: NodeRef) -> bool {
        match self.node_kind(location) {
            AstKind::TSPropertySignature(_)
            | AstKind::PropertyDefinition(_)
            | AstKind::TSTypeAliasDeclaration(_)
            | AstKind::FormalParameter(_)
            | AstKind::FormalParameterRest(_)
            | AstKind::TSThisParameter(_) => true,
            AstKind::BindingIdentifier(_) => self
                .nodes(location.program_id)
                .ancestor_kinds(location.node_id)
                .any(|kind| {
                    matches!(
                        kind,
                        AstKind::FormalParameter(_)
                            | AstKind::FormalParameterRest(_)
                            | AstKind::TSThisParameter(_)
                    )
                }),
            _ => false,
        }
    }

    fn type_alias_target_for_display(
        &self,
        ty: Ty<'a>,
        context: TypeStringContext,
    ) -> Option<Ty<'a>> {
        let metadata = self.type_alias_metadata(ty)?;
        let is_default_lib_alias = self
            .store
            .entry(metadata.declaration.program_id)
            .is_some_and(program::ProgramEntry::is_lib);
        if !is_default_lib_alias && !context.expands_transparent_aliases() {
            return None;
        }
        let TypeData::TypeReference(reference) = self.arena().type_data(ty) else {
            return None;
        };
        let AstKind::TSTypeAliasDeclaration(alias) = self
            .nodes(metadata.declaration.program_id)
            .kind(metadata.declaration.node_id)
        else {
            return None;
        };
        if !is_default_lib_alias && matches!(&alias.type_annotation, TSType::TSUnionType(_)) {
            return None;
        }
        let substitutions = self.type_parameter_substitutions_for_reference(
            metadata.declaration.program_id,
            alias.type_parameters.as_deref(),
            reference,
        );
        let target =
            self.get_type_from_ts_type(metadata.declaration.program_id, &alias.type_annotation);
        Some(self.instantiate_type(target, &substitutions.to_mapper(self.arena())))
    }

    fn transparent_type_alias_target(
        &self,
        ty: Ty<'a>,
        context: TypeStringContext,
    ) -> Option<Ty<'a>> {
        let target = self.type_alias_target_for_display(ty, context)?;
        if target.is_transparent_type_alias_union_constituent(self.arena()) {
            return Some(target);
        }

        let is_non_generic_alias = self.type_alias_metadata(ty).is_some_and(|metadata| {
            matches!(
                self.nodes(metadata.declaration.program_id)
                    .kind(metadata.declaration.node_id),
                AstKind::TSTypeAliasDeclaration(alias)
                    if alias
                        .type_parameters
                        .as_ref()
                        .is_none_or(|type_parameters| type_parameters.params.is_empty())
            )
        });
        (is_non_generic_alias
            && context.expands_transparent_aliases()
            && matches!(
                self.arena().type_data(target),
                TypeData::TypeReference(reference) if reference.type_arguments.is_empty()
            ))
        .then_some(target)
    }

    fn location_expands_named_type_alias_chains(&self, location: NodeRef) -> bool {
        matches!(
            self.node_kind(location),
            AstKind::TSPropertySignature(_) | AstKind::PropertyDefinition(_)
        )
    }

    fn type_alias_chain_display_replacements(
        &self,
        ty: Ty<'a>,
        context: TypeStringContext,
    ) -> HashMap<Ty<'a>, Ty<'a>> {
        let mut replacements = HashMap::new();
        if !context.expand_named_alias_chains {
            return replacements;
        }
        self.collect_type_alias_chain_display_replacements(ty, context, &mut replacements);
        replacements
    }

    fn collect_type_alias_chain_display_replacements(
        &self,
        ty: Ty<'a>,
        context: TypeStringContext,
        replacements: &mut HashMap<Ty<'a>, Ty<'a>>,
    ) {
        if matches!(self.arena().type_data(ty), TypeData::TypeReference(_)) {
            self.insert_type_alias_chain_display_replacements(ty, context, replacements);
        }

        // TypeScript forwards alias wrappers through these exposed structural positions, but not
        // through members of an anonymous object type.
        let children = match self.arena().type_data(ty) {
            TypeData::TypeReference(reference) => {
                reference.type_arguments.iter().copied().collect()
            }
            TypeData::Array(array) => vec![array.element_type],
            TypeData::Tuple(tuple) => tuple.elements.iter().map(TupleElement::ty).collect(),
            TypeData::Union(union) => union.types.iter().copied().collect(),
            _ => Vec::new(),
        };
        for child in children {
            self.collect_type_alias_chain_display_replacements(child, context, replacements);
        }
    }

    fn insert_type_alias_chain_display_replacements(
        &self,
        ty: Ty<'a>,
        context: TypeStringContext,
        replacements: &mut HashMap<Ty<'a>, Ty<'a>>,
    ) {
        let mut current = ty;
        let mut seen = HashSet::new();
        while seen.insert(current) {
            let Some(target) = self.type_alias_target_for_display(current, context) else {
                return;
            };
            if !matches!(self.arena().type_data(target), TypeData::TypeReference(_))
                || self.type_alias_metadata(target).is_none()
            {
                return;
            }
            if target == current {
                return;
            }
            replacements.insert(current, target);
            current = target;
        }

        // TODO(correctness): validate named-alias chain display in non-property formatter
        // positions before widening the location policy.
    }
}

fn transparent_type_alias_type_parameter_name<'a>(ty: &'a TSType<'a>) -> Option<&'a str> {
    match ty {
        TSType::TSTypeReference(reference)
            if reference
                .type_arguments
                .as_ref()
                .is_none_or(|arguments| arguments.params.is_empty()) =>
        {
            match &reference.type_name {
                TSTypeName::IdentifierReference(identifier) => Some(identifier.name.as_str()),
                _ => None,
            }
        }
        TSType::TSParenthesizedType(parenthesized) => {
            transparent_type_alias_type_parameter_name(&parenthesized.type_annotation)
        }
        _ => None,
    }
}

fn is_const_type_reference(ty: &TSType<'_>) -> bool {
    match ty {
        TSType::TSTypeReference(reference)
            if reference
                .type_arguments
                .as_ref()
                .is_none_or(|arguments| arguments.params.is_empty()) =>
        {
            matches!(
                &reference.type_name,
                TSTypeName::IdentifierReference(identifier) if identifier.name == "const"
            )
        }
        TSType::TSParenthesizedType(parenthesized) => {
            is_const_type_reference(&parenthesized.type_annotation)
        }
        _ => false,
    }
}

fn type_contains_literal_type<'a>(arena: CheckerArena<'a>, ty: Ty<'a>, depth: usize) -> bool {
    if depth >= TYPE_EXPANSION_MAX_DEPTH {
        return false;
    }

    match arena.type_data(ty) {
        TypeData::StringLiteral(_)
        | TypeData::NumberLiteral(_)
        | TypeData::BooleanLiteral(_)
        | TypeData::BigIntLiteral(_)
        | TypeData::TemplateLiteral(_) => true,
        TypeData::Object(object) => object
            .properties
            .iter()
            .any(|property| type_contains_literal_type(arena, property.ty, depth + 1)),
        TypeData::Array(array) => type_contains_literal_type(arena, array.element_type, depth + 1),
        TypeData::Tuple(tuple) => tuple
            .elements
            .iter()
            .any(|element| type_contains_literal_type(arena, element.ty(), depth + 1)),
        TypeData::Union(union) => union
            .types
            .iter()
            .any(|ty| type_contains_literal_type(arena, *ty, depth + 1)),
        TypeData::Intersection(intersection) => intersection
            .types
            .iter()
            .any(|ty| type_contains_literal_type(arena, *ty, depth + 1)),
        _ => false,
    }
}

impl<'a> Checker<'a> for CheckerReturn<'a, '_> {
    fn get_symbol_at_location(&self, node: NodeRef) -> Option<SymbolRef> {
        match self.node_kind(node) {
            AstKind::BindingIdentifier(identifier) => identifier
                .symbol_id
                .get()
                .map(|symbol_id| SymbolRef::new(node.program_id, symbol_id)),
            AstKind::IdentifierReference(identifier) => self
                .symbol_for_identifier_reference(node.program_id, identifier)
                .or_else(|| {
                    self.get_value_symbol_for_name(node.program_id, identifier.name.as_str())
                })
                .or_else(|| {
                    self.get_type_symbol_for_export_specifier_local(
                        node.program_id,
                        node.node_id,
                        identifier,
                    )
                }),
            AstKind::TSTypeReference(reference) => match &reference.type_name {
                TSTypeName::IdentifierReference(identifier) => self
                    .symbol_for_identifier_reference(node.program_id, identifier)
                    .or_else(|| {
                        self.get_value_symbol_for_name(node.program_id, identifier.name.as_str())
                            .or_else(|| {
                                self.get_type_symbol_for_name(
                                    node.program_id,
                                    identifier.name.as_str(),
                                )
                            })
                    }),
                _ => None,
            },
            _ => None,
        }
    }

    fn get_type_at_location(&self, node: NodeRef) -> Ty<'a> {
        match self.node_kind(node) {
            expression_kind @ (AstKind::IdentifierReference(_)
            | AstKind::ThisExpression(_)
            | AstKind::ArrayExpression(_)
            | AstKind::ObjectExpression(_)
            | AstKind::TemplateLiteral(_)
            | AstKind::TaggedTemplateExpression(_)
            | AstKind::PrivateFieldExpression(_)
            | AstKind::CallExpression(_)
            | AstKind::NewExpression(_)
            | AstKind::ImportMeta(_)
            | AstKind::NewTarget(_)
            | AstKind::UpdateExpression(_)
            | AstKind::UnaryExpression(_)
            | AstKind::BinaryExpression(_)
            | AstKind::PrivateInExpression(_)
            | AstKind::LogicalExpression(_)
            | AstKind::ConditionalExpression(_)
            | AstKind::AssignmentExpression(_)
            | AstKind::SequenceExpression(_)
            | AstKind::Super(_)
            | AstKind::AwaitExpression(_)
            | AstKind::ChainExpression(_)
            | AstKind::ParenthesizedExpression(_)
            | AstKind::ArrowFunctionExpression(_)
            | AstKind::YieldExpression(_)
            | AstKind::ImportExpression(_)
            | AstKind::V8IntrinsicExpression(_)
            | AstKind::BooleanLiteral(_)
            | AstKind::NullLiteral(_)
            | AstKind::NumericLiteral(_)
            | AstKind::StringLiteral(_)
            | AstKind::BigIntLiteral(_)
            | AstKind::RegExpLiteral(_)
            | AstKind::JSXElement(_)
            | AstKind::JSXFragment(_)
            | AstKind::TSAsExpression(_)
            | AstKind::TSSatisfiesExpression(_)
            | AstKind::TSTypeAssertion(_)
            | AstKind::TSNonNullExpression(_)
            | AstKind::TSInstantiationExpression(_)
            | AstKind::StaticMemberExpression(_)
            | AstKind::ComputedMemberExpression(_)) => self.check_expression_with_context(
                node.program_id,
                expression_kind,
                Some(node.node_id),
                ExpressionCheckContext::new(GetTypeFlags::PRESERVE_LITERALS),
            ),
            expression_kind @ AstKind::Function(function) if function.is_expression() => self
                .check_expression_with_context(
                    node.program_id,
                    expression_kind,
                    Some(node.node_id),
                    ExpressionCheckContext::new(GetTypeFlags::PRESERVE_LITERALS),
                ),
            expression_kind @ AstKind::Class(class) if class.is_expression() => self
                .check_expression_with_context(
                    node.program_id,
                    expression_kind,
                    Some(node.node_id),
                    ExpressionCheckContext::new(GetTypeFlags::PRESERVE_LITERALS),
                ),
            AstKind::Directive(directive) => Ty::string_literal(
                self.arena(),
                self.get_string_literal_value(&directive.expression),
            ),
            AstKind::BindingIdentifier(identifier) => {
                if let AstKind::TSTypeAliasDeclaration(alias) =
                    self.nodes(node.program_id).parent_kind(node.node_id)
                {
                    self.get_type_of_type_alias_declaration(node.program_id, alias)
                } else if let AstKind::Class(class) =
                    self.nodes(node.program_id).parent_kind(node.node_id)
                    && self.is_later_duplicate_class_declaration(node.program_id, class)
                {
                    self.get_type_of_duplicate_class_declaration(node.program_id, class)
                } else {
                    identifier.symbol_id.get().map_or_else(
                        || {
                            self.get_type_of_binding_identifier_without_symbol(
                                node.program_id,
                                node.node_id,
                            )
                        },
                        |symbol_id| {
                            let ty =
                                self.get_type_of_symbol(SymbolRef::new(node.program_id, symbol_id));
                            let has_type_query_annotation = matches!(
                                self.nodes(node.program_id).parent_kind(node.node_id),
                                AstKind::VariableDeclarator(declarator)
                                    if declarator.type_annotation.as_deref().is_some_and(
                                        |annotation| {
                                            matches!(
                                                annotation.type_annotation,
                                                TSType::TSTypeQuery(_)
                                            )
                                        }
                                    )
                            );
                            if has_type_query_annotation
                                && let TypeData::TypeQuery(query) = self.arena().type_data(ty)
                                && matches!(
                                    self.arena().type_data(query.resolved),
                                    TypeData::Object(_)
                                )
                            {
                                query.resolved
                            } else {
                                ty
                            }
                        },
                    )
                }
            }
            AstKind::TSPropertySignature(property) => {
                let ty = property
                    .type_annotation
                    .as_deref()
                    .map_or_else(Ty::any, |annotation| {
                        self.get_type_from_property_signature_annotation(
                            node.program_id,
                            annotation,
                        )
                    });
                let ty = if let TypeData::Infer(infer) = self.arena().type_data(ty) {
                    Ty::type_reference(self.arena(), infer.type_parameter.name, [])
                } else {
                    ty
                };
                if property.optional {
                    ty.or_undefined(self.arena())
                } else {
                    ty
                }
            }
            AstKind::TSMethodSignature(method) => {
                self.get_type_of_ts_method_signature_location(node.program_id, node.node_id, method)
            }
            AstKind::FormalParameter(parameter) => {
                parameter.type_annotation.as_deref().map_or_else(
                    || {
                        self.get_contextual_type_of_formal_parameter(
                            node.program_id,
                            node.node_id,
                            parameter,
                        )
                        .unwrap_or_else(Ty::any)
                    },
                    |annotation| {
                        self.get_declared_type_of_formal_parameter(
                            node.program_id,
                            parameter,
                            annotation,
                        )
                    },
                )
            }
            AstKind::FormalParameterRest(parameter) => self
                .get_parameter_type_from_ts_type_annotation(
                    node.program_id,
                    parameter.type_annotation.as_deref(),
                ),
            AstKind::TSThisParameter(parameter) => self.get_parameter_type_from_ts_type_annotation(
                node.program_id,
                parameter.type_annotation.as_deref(),
            ),
            AstKind::IdentifierName(_)
                if matches!(
                    self.nodes(node.program_id).parent_kind(node.node_id),
                    AstKind::ImportMeta(_) | AstKind::NewTarget(_)
                ) =>
            {
                let parent_id = self.nodes(node.program_id).parent_id(node.node_id);
                self.get_type_at_location(NodeRef::new(node.program_id, parent_id))
            }
            AstKind::IdentifierName(_)
                if matches!(
                    self.nodes(node.program_id).parent_kind(node.node_id),
                    AstKind::TSImportType(_)
                ) =>
            {
                Ty::any()
            }
            AstKind::IdentifierName(identifier)
                if matches!(
                    self.nodes(node.program_id).parent_kind(node.node_id),
                    AstKind::TSImportTypeQualifiedName(qualified)
                        if qualified.right.span != identifier.span
                ) =>
            {
                self.get_type_of_ts_import_type_qualifier_identifier(
                    node.program_id,
                    node.node_id,
                    identifier.name.as_str(),
                )
            }
            AstKind::IdentifierName(_)
                if matches!(
                    self.nodes(node.program_id).parent_kind(node.node_id),
                    AstKind::TSImportTypeQualifiedName(_)
                ) =>
            {
                Ty::any()
            }
            AstKind::IdentifierName(identifier)
                if matches!(
                    self.nodes(node.program_id).parent_kind(node.node_id),
                    AstKind::TSTypePredicate(_)
                ) =>
            {
                self.get_type_of_type_predicate_identifier(
                    node.program_id,
                    node.node_id,
                    identifier.name.as_str(),
                )
            }
            AstKind::ObjectProperty(property) => {
                let in_const_context = self.is_in_const_context(node.program_id, node.node_id);
                let contextual_type = self.get_contextual_type_of_object_property_value(
                    node.program_id,
                    node.node_id,
                    property.value.span(),
                );
                let flags = if in_const_context
                    || (matches!(property.value, Expression::BooleanLiteral(_))
                        && self.is_in_contextually_typed_initializer(node.program_id, node.node_id))
                    || contextual_type
                        .is_some_and(|ty| type_contains_literal_type(self.arena(), ty, 0))
                {
                    GetTypeFlags::PRESERVE_LITERALS
                } else {
                    GetTypeFlags::NONE
                };
                let mut context = ExpressionCheckContext::new(flags);
                if let Some(contextual_type) = contextual_type {
                    context = context.with_contextual_type(contextual_type, CheckMode::CONTEXTUAL);
                }
                if in_const_context {
                    context =
                        context.with_check_mode(CheckMode::CONST_CONTEXT | CheckMode::FORCE_TUPLE);
                }
                self.check_expression_with_context(
                    node.program_id,
                    AstKind::from_expression(&property.value),
                    Some(node.node_id),
                    context,
                )
            }
            AstKind::ExpressionStatement(expr) => self.get_type_of_expression_with_node(
                node.program_id,
                &expr.expression,
                Some(node.node_id),
                GetTypeFlags::PRESERVE_LITERALS,
            ),
            AstKind::MethodDefinition(method) => {
                let class = self
                    .nodes(node.program_id)
                    .ancestor_kinds(method.node_id())
                    .find(|kind| matches!(kind, AstKind::Class(_)));
                if let Some(AstKind::Class(class)) = class {
                    self.get_type_of_method_definition(node.program_id, method, class.node_id())
                } else {
                    Ty::none()
                }
            }
            AstKind::PropertyDefinition(property) => {
                self.get_type_of_property_definition(node.program_id, property, Some(node.node_id))
            }
            AstKind::TSTypeAliasDeclaration(alias) => {
                let ty = self.get_type_of_type_alias_declaration(node.program_id, alias);
                if ty.is_none() { Ty::any() } else { ty }
            }
            AstKind::TSEnumDeclaration(declaration) => {
                self.get_type_of_enum_declaration(node.program_id, declaration)
            }
            AstKind::TSEnumMember(member) => self.get_type_of_enum_member(node.program_id, member),
            AstKind::TSImportEqualsDeclaration(_) => Ty::any(),
            AstKind::TSInterfaceDeclaration(_) => Ty::any(),
            AstKind::ExportSpecifier(specifier) => {
                self.get_type_of_export_specifier_local(node.program_id, specifier)
            }
            AstKind::TSModuleDeclaration(module) => {
                let TSModuleDeclarationName::Identifier(identifier) = &module.id else {
                    return Ty::none();
                };
                // TODO(correctness): model namespace value-side as a real module namespace
                // type instead of an `any` stub. The `TypeQuery` wrapper preserves the
                // `typeof Module` display used by TypeScript for namespace declarations.
                Ty::type_query(
                    self.arena(),
                    identifier.name.as_str(),
                    Ty::any(),
                    std::iter::empty(),
                )
            }
            AstKind::TSTypeParameter(_) => Ty::any(),
            AstKind::TSMappedType(_) => Ty::any(),
            AstKind::TSClassImplements(_) => Ty::any(),
            AstKind::TSInterfaceHeritage(heritage) => {
                let Expression::Identifier(identifier) = &heritage.expression else {
                    return Ty::any();
                };
                self.symbol_for_identifier_reference(node.program_id, identifier)
                    .or_else(|| {
                        self.get_value_symbol_for_name(node.program_id, identifier.name.as_str())
                    })
                    .map_or_else(Ty::any, |symbol| {
                        let ty = self.get_type_of_symbol(symbol);
                        if ty.is_none() { Ty::any() } else { ty }
                    })
            }
            AstKind::TSTypeReference(reference)
                if matches!(reference.type_name, TSTypeName::QualifiedName(_)) =>
            {
                self.get_type_from_ts_type_reference(node.program_id, reference)
            }
            AstKind::TSTypeReference(_) => {
                let ty = self
                    .get_symbol_at_location(node)
                    .map_or_else(Ty::any, |symbol| self.get_type_of_symbol(symbol));
                if ty.is_none() { Ty::any() } else { ty }
            }
            AstKind::TSIndexSignatureName(signature_name) => self.get_type_from_ts_type_annotation(
                node.program_id,
                Some(&signature_name.type_annotation),
            ),
            _ => self
                .get_symbol_at_location(node)
                .map_or_else(Ty::none, |sym| self.get_type_of_symbol(sym)),
        }
    }

    fn get_constrained_type_at_location(&self, node: NodeRef) -> Ty<'a> {
        let ty = self.get_type_at_location(node);
        self.get_type_parameter_constraint(node.program_id, node.node_id, ty)
            .unwrap_or(ty)
    }

    fn get_declared_type_of_symbol(&self, sym: SymbolRef) -> Ty<'a> {
        if let Some(ty) = self
            .declared_type_cache
            .borrow()
            .get(sym.program_id.index())
            .and_then(Option::as_ref)
            .and_then(|cache| cache.get(sym.symbol_id))
            .copied()
            .flatten()
        {
            return ty;
        }

        let ty = if let Some((declaration, declarator)) = self.variable_declarator_for_symbol(sym) {
            return self
                .get_type_of_binding_pattern(
                    sym.program_id,
                    declaration,
                    BindingPatternKind::VariableDeclarator(declarator),
                    sym.symbol_id,
                )
                .unwrap_or_else(|| {
                    self.get_type_of_variable_declarator(sym.program_id, declaration, declarator)
                });
        } else {
            let declaration = self
                .semantic(sym.program_id)
                .scoping()
                .symbol_declaration(sym.symbol_id);
            match self.nodes(sym.program_id).kind(declaration) {
                AstKind::VariableDeclarator(declarator) => self
                    .get_type_of_binding_pattern(
                        sym.program_id,
                        declaration,
                        BindingPatternKind::VariableDeclarator(declarator),
                        sym.symbol_id,
                    )
                    .unwrap_or_else(|| {
                        self.get_type_of_variable_declarator(
                            sym.program_id,
                            declaration,
                            declarator,
                        )
                    }),
                AstKind::FormalParameter(parameter) => self
                    .get_type_of_binding_pattern(
                        sym.program_id,
                        declaration,
                        BindingPatternKind::FormalParameter(parameter),
                        sym.symbol_id,
                    )
                    .unwrap_or_else(|| match parameter.type_annotation.as_deref() {
                        Some(annotation) => self.get_declared_type_of_formal_parameter(
                            sym.program_id,
                            parameter,
                            annotation,
                        ),
                        None => self
                            .get_contextual_type_of_formal_parameter(
                                sym.program_id,
                                declaration,
                                parameter,
                            )
                            .unwrap_or_else(Ty::any),
                    }),
                AstKind::FormalParameterRest(parameter) => self
                    .get_type_of_binding_pattern(
                        sym.program_id,
                        declaration,
                        BindingPatternKind::RestParameter(parameter),
                        sym.symbol_id,
                    )
                    .unwrap_or_else(|| {
                        self.get_type_from_ts_type_annotation(
                            sym.program_id,
                            parameter.type_annotation.as_deref(),
                        )
                    }),
                AstKind::CatchParameter(parameter) => parameter
                    .type_annotation
                    .as_deref()
                    .map_or_else(Ty::unknown, |annotation| {
                        self.get_type_from_ts_type_annotation(sym.program_id, Some(annotation))
                    }),
                AstKind::PropertyDefinition(property) => self.get_type_of_property_definition(
                    sym.program_id,
                    property,
                    Some(declaration),
                ),
                AstKind::Function(function) => self.get_type_of_function_declaration_group(
                    sym.program_id,
                    function,
                    declaration,
                ),
                AstKind::ArrowFunctionExpression(arrow_func_expr) => self
                    .get_type_of_function_signature_with_node(
                        sym.program_id,
                        FunctionKind::ArrowFunction(arrow_func_expr),
                        Some(declaration),
                    ),
                AstKind::AccessorProperty(property) => self.get_type_from_ts_type_annotation(
                    sym.program_id,
                    property.type_annotation.as_deref(),
                ),
                AstKind::TSTypeAliasDeclaration(alias)
                    if matches!(alias.type_annotation, TSType::TSTypeQuery(_)) =>
                {
                    self.get_type_of_type_alias_declaration(sym.program_id, alias)
                }
                AstKind::TSTypeAliasDeclaration(_) => Ty::none(),
                AstKind::TSEnumDeclaration(declaration) => {
                    self.get_type_of_enum_declaration(sym.program_id, declaration)
                }
                AstKind::TSModuleDeclaration(module) => match &module.id {
                    TSModuleDeclarationName::Identifier(identifier) => Ty::type_query(
                        self.arena(),
                        identifier.name.as_str(),
                        Ty::any(),
                        std::iter::empty(),
                    ),
                    TSModuleDeclarationName::StringLiteral(_) => Ty::none(),
                },
                AstKind::BindingIdentifier(identifier) => {
                    if let Some(ty) = self.get_type_of_binding_identifier_from_binding_pattern(
                        sym.program_id,
                        declaration,
                        sym.symbol_id,
                    ) {
                        return ty;
                    }

                    match self.nodes(sym.program_id).parent_kind(declaration) {
                        AstKind::Class(_) => {
                            // TODO(correctness): model the class value-side as a real constructor
                            // object type instead of a `Ty::any` stub. Today the `Ty::TypeQuery`
                            // name field is what downstream class-static lookups key off.
                            Ty::type_query(
                                self.arena(),
                                identifier.name.as_str(),
                                Ty::any(),
                                std::iter::empty(),
                            )
                        }
                        AstKind::Function(function) => self.get_type_of_function_declaration_group(
                            sym.program_id,
                            function,
                            self.nodes(sym.program_id).parent_id(declaration),
                        ),
                        AstKind::VariableDeclarator(declarator) => self
                            .get_type_of_variable_declarator(
                                sym.program_id,
                                self.nodes(sym.program_id).parent_id(declaration),
                                declarator,
                            ),
                        AstKind::ArrowFunctionExpression(arrow_func_expr) => self
                            .get_type_of_function_signature_with_node(
                                sym.program_id,
                                FunctionKind::ArrowFunction(arrow_func_expr),
                                Some(declaration),
                            ),
                        AstKind::TSTypeAliasDeclaration(alias)
                            if matches!(alias.type_annotation, TSType::TSTypeQuery(_)) =>
                        {
                            self.get_type_of_type_alias_declaration(sym.program_id, alias)
                        }
                        AstKind::TSTypeAliasDeclaration(_) => Ty::none(),
                        AstKind::TSEnumDeclaration(declaration) => {
                            self.get_type_of_enum_declaration(sym.program_id, declaration)
                        }
                        AstKind::TSModuleDeclaration(module) => match &module.id {
                            TSModuleDeclarationName::Identifier(module_name) => Ty::type_query(
                                self.arena(),
                                module_name.name.as_str(),
                                Ty::any(),
                                std::iter::empty(),
                            ),
                            TSModuleDeclarationName::StringLiteral(_) => Ty::none(),
                        },
                        _ => Ty::none(),
                    }
                }
                AstKind::Class(class) => class.id.as_ref().map_or_else(Ty::any, |identifier| {
                    // TODO(correctness): same as above—replace `Ty::any` stub with a real
                    // constructor object type for the class.
                    Ty::type_query(
                        self.arena(),
                        identifier.name.as_str(),
                        Ty::any(),
                        std::iter::empty(),
                    )
                }),
                // TODO
                AstKind::ImportSpecifier(_)
                | AstKind::ImportDefaultSpecifier(_)
                | AstKind::ImportNamespaceSpecifier(_) => Ty::any(),
                AstKind::TSImportEqualsDeclaration(_) => Ty::any(),
                _ => Ty::none(),
            }
        };

        if let Some(program_cache) = self
            .declared_type_cache
            .borrow_mut()
            .get_mut(sym.program_id.index())
        {
            let cache = program_cache.get_or_insert_with(|| {
                IndexVec::from_vec(vec![
                    None;
                    self.semantic(sym.program_id).scoping().symbols_len()
                ])
            });
            if let Some(slot) = cache.get_mut(sym.symbol_id) {
                *slot = Some(ty);
            }
        }
        ty
    }

    fn get_type_of_symbol(&self, sym: SymbolRef) -> Ty<'a> {
        if let Some(ty) = self
            .value_type_cache
            .borrow()
            .get(sym.program_id.index())
            .and_then(Option::as_ref)
            .and_then(|cache| cache.get(sym.symbol_id))
            .copied()
            .flatten()
        {
            return ty;
        }

        {
            let mut resolving_symbols = self.resolving_symbols.borrow_mut();
            if resolving_symbols.contains(&sym) {
                return Ty::error(self.arena(), TypeErrorKind::UnresolvedType);
            }
            resolving_symbols.push(sym);
        }

        let ty = if let Some(imported_type) = self.get_type_of_import_symbol(sym) {
            imported_type
        } else {
            match self
                .semantic(sym.program_id)
                .symbol_declaration(sym.symbol_id)
                .kind()
            {
                AstKind::VariableDeclarator(declarator) => {
                    let declaration = self
                        .semantic(sym.program_id)
                        .scoping()
                        .symbol_declaration(sym.symbol_id);
                    self.get_type_of_binding_pattern(
                        sym.program_id,
                        declaration,
                        BindingPatternKind::VariableDeclarator(declarator),
                        sym.symbol_id,
                    )
                    .unwrap_or_else(|| {
                        self.get_type_of_variable_declarator(
                            sym.program_id,
                            declaration,
                            declarator,
                        )
                    })
                }
                _ => self.get_declared_type_of_symbol(sym),
            }
        };

        self.resolving_symbols.borrow_mut().pop();
        if let Some(program_cache) = self
            .value_type_cache
            .borrow_mut()
            .get_mut(sym.program_id.index())
        {
            let cache = program_cache.get_or_insert_with(|| {
                IndexVec::from_vec(vec![
                    None;
                    self.semantic(sym.program_id).scoping().symbols_len()
                ])
            });
            if let Some(slot) = cache.get_mut(sym.symbol_id) {
                *slot = Some(ty);
            }
        }
        ty
    }

    // TODO(completeness): Implement this method
    fn get_type_of_symbol_at_location(&self, node: NodeRef) -> Ty<'a> {
        self.get_type_at_location(node)
    }

    // TODO(completeness): Implement this method
    fn get_properties_of_type(&self, _t: Ty<'a>) -> Vec<SymbolRef> {
        Vec::new()
    }

    // TODO(completeness): Implement this method
    fn get_property_of_type(&self, _t: Ty<'a>, _name: &str) -> Option<SymbolRef> {
        None
    }

    fn get_signatures_of_type(&self, t: Ty<'a>, kind: SignatureKind) -> Vec<Signature<'a>> {
        match self.arena().type_data(t) {
            TypeData::Function(_) if kind == SignatureKind::Call => {
                vec![Signature::new(SignatureKind::Call, t)]
            }
            TypeData::Object(object) => object
                .signatures
                .iter()
                .copied()
                .filter(|signature| signature.kind == kind)
                .collect(),
            TypeData::Intersection(intersection) => {
                // TODO(overloads): TypeScript Go combines intersection signatures with
                // `CompositeSignature` metadata. Concatenation is conservative enough for
                // first-pass call resolution but loses combined type predicate/diagnostic data.
                intersection
                    .types
                    .iter()
                    .flat_map(|ty| self.get_signatures_of_type(*ty, kind))
                    .collect()
            }
            TypeData::Union(union) => {
                // TODO(overloads): union call signatures need TypeScript Go's matching-signature
                // synthesis. Returning all candidates can over-accept some invalid union calls.
                union
                    .types
                    .iter()
                    .flat_map(|ty| self.get_signatures_of_type(*ty, kind))
                    .collect()
            }
            _ => Vec::new(),
        }
    }

    fn get_index_infos_of_type(&self, t: Ty<'a>) -> Vec<IndexInfo<'a>> {
        match self.arena().type_data(t) {
            TypeData::Object(object) => object.index_infos.iter().copied().collect(),
            TypeData::Intersection(intersection) => intersection
                .types
                .iter()
                .flat_map(|ty| self.get_index_infos_of_type(*ty))
                .collect(),
            TypeData::Union(union) => union
                .types
                .iter()
                .flat_map(|ty| self.get_index_infos_of_type(*ty))
                .collect(),
            _ => Vec::new(),
        }
    }

    fn is_assignable_to(&self, source: Ty<'a>, target: Ty<'a>) -> bool {
        CheckerReturn::is_assignable_to(self, source, target)
    }

    fn type_to_string(&self, t: Ty<'a>, location: NodeRef) -> String {
        self.type_to_string_with_context(t, self.type_string_context_at_location(location))
    }

    fn symbol_to_string(&self, s: SymbolRef, _location: NodeRef) -> String {
        self.semantic(s.program_id)
            .scoping()
            .symbol_name(s.symbol_id)
            .to_string()
    }
}
