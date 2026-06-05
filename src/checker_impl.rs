use bitflags::bitflags;
use oxc_ast::{
    AstKind,
    ast::{
        ArrayExpression, ArrayExpressionElement, ArrowFunctionExpression, AssignmentExpression,
        AwaitExpression, BigIntLiteral, BinaryExpression, BindingPattern, CallExpression, Class,
        ClassElement, ComputedMemberExpression, ConditionalExpression, Expression, FormalParameter,
        FormalParameterRest, FormalParameters, Function, IdentifierReference, MethodDefinition,
        MethodDefinitionKind, NewExpression, ObjectExpression, ObjectPropertyKind,
        PropertyDefinition, StaticMemberExpression, StringLiteral, TSInterfaceDeclaration,
        TSLiteral, TSMappedType, TSModuleDeclarationName, TSSignature, TSThisParameter,
        TSTupleElement, TSType, TSTypeAnnotation, TSTypeName, TSTypeOperatorOperator,
        TSTypeParameter, TSTypeQuery, TSTypeQueryExprName, TSTypeReference,
        VariableDeclarationKind, VariableDeclarator,
    },
};
use oxc_semantic::{AstNodes, NodeId, Semantic, SymbolId};
use oxc_span::{GetSpan, Span};
use oxc_str::{Ident, static_ident};
use oxc_syntax::{
    module_record::{ExportExportName, ExportLocalName},
    operator::{AssignmentOperator, BinaryOperator, UnaryOperator},
};
use std::collections::{HashMap, HashSet};

use crate::{
    TemplateLiteralElement, binding_pattern_default_initializer_symbol_id,
    checker::{Checker, CheckerReturn, ClassMemberResolution, NodeRef, SymbolRef},
    evolving_arrays, flow, for_statement_left_contains_declarator, index_signature_key_types,
    index_type_to_property_name,
    infer::ts_type_contains_infer,
    is_iterable_type_reference, is_mapped_empty_object_intersection,
    is_promise_like_type_reference,
    program::{self},
    property_key_name_str, push_type_parameter_names, relations, ts_type_name_to_str,
    ts_type_query_expr_name_to_str, tuple_element_type_at_index, tuple_index_from_expression,
    types::{
        CheckerArena, IndexInfo, MappedModifier, Signature, SignatureKind, TupleElement, Ty,
        TyFunction, TyMapped, TyParameter, TyProperty, TyTypeParameter, TyTypePredicate,
        TyTypeQuery, TyTypeReference, binding_pattern_to_parameter_name,
        return_type_and_type_predicate_from_annotation_with_resolver, type_predicate_return_type,
    },
};

pub const UNDEFINED_IDENT: Ident = static_ident!("undefined");
const TYPE_EXPANSION_MAX_DEPTH: usize = 32;

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
}

bitflags! {
    /// Flags for changing behavior when getting the types of expressions or nodes.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) struct GetTypeFlags: u8 {
        const NONE = 0;
        /// Indicates that when literals are encountered, they should be preserved instead of widened
        /// to a more general type. For example: prefer `123` over `number`, `"foo"` over `string`.
        const PRESERVE_LITERALS = 1 << 0;
    }
}

impl GetTypeFlags {
    pub fn preserve_literals(&self) -> bool {
        self.contains(GetTypeFlags::PRESERVE_LITERALS)
    }
}

impl<'a, 'store> CheckerReturn<'a, 'store> {
    #[inline]
    pub fn entry(&self, program_id: program::ProgramId) -> &program::ProgramEntry<'a> {
        self.store
            .entry(program_id)
            .expect("store-backed checker must reference a valid program")
    }

    #[inline]
    pub fn semantic(&self, program_id: program::ProgramId) -> &Semantic<'a> {
        self.entry(program_id).semantic()
    }

    #[inline]
    pub fn nodes(&self, program_id: program::ProgramId) -> &AstNodes<'a> {
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

    /// Resolve an expression type with a semantic context node when ancestor context is needed.
    /// This keeps `this` and member expressions tied to the class or call site they appear in.
    pub(crate) fn get_type_of_expression_with_node(
        &self,
        program_id: program::ProgramId,
        expression: &'a Expression<'a>,
        node_id: Option<NodeId>,
        flags: GetTypeFlags,
    ) -> Ty<'a> {
        match expression {
            Expression::Identifier(identifier) => {
                let symbol = identifier
                    .reference_id
                    .get()
                    .and_then(|reference_id| {
                        self.semantic(program_id)
                            .scoping()
                            .get_reference(reference_id)
                            .symbol_id()
                    })
                    .map(|symbol_id| SymbolRef::new(program_id, symbol_id))
                    .or_else(|| {
                        self.get_value_symbol_for_name(program_id, identifier.name.as_str())
                    });
                if let Some(symbol) = symbol {
                    let base_type = self.get_type_of_symbol(symbol);
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
                Ty::any()
            }
            Expression::ObjectExpression(object) => {
                self.get_type_of_object_expression(program_id, object, node_id)
            }
            Expression::BinaryExpression(binary_expression) => {
                self.get_type_of_binary_expression(program_id, binary_expression, node_id)
            }
            Expression::AssignmentExpression(assignment_expression) => {
                self.get_type_of_assignment_expression(program_id, assignment_expression, node_id)
            }
            Expression::ConditionalExpression(conditional) => {
                self.get_type_of_conditional_expression(program_id, conditional, node_id)
            }
            Expression::UnaryExpression(unary_expression) => match unary_expression.operator {
                UnaryOperator::UnaryNegation => match &unary_expression.argument {
                    Expression::NumericLiteral(literal) if flags.preserve_literals() => {
                        let name = self.arena().str(&format!("-{}", literal.raw_str()));
                        Ty::number_literal(self.arena(), name)
                    }
                    _ => Ty::number(),
                },
                UnaryOperator::UnaryPlus => match &unary_expression.argument {
                    Expression::NumericLiteral(literal) if flags.preserve_literals() => {
                        let name = self.arena().str(&literal.raw_str());
                        Ty::number_literal(self.arena(), name)
                    }
                    _ => Ty::number(),
                },
                UnaryOperator::BitwiseNot => Ty::number(),
                // TODO(correctness): add const eval for `!` expressions to boolean literals
                UnaryOperator::LogicalNot => Ty::boolean(),
                UnaryOperator::Typeof => Ty::typeof_string_values(self.arena()),
                UnaryOperator::Void => Ty::undefined(),
                UnaryOperator::Delete => Ty::boolean(),
            },
            Expression::TSNonNullExpression(non_null_expr) => {
                let ty = self.get_type_of_expression_with_node(
                    program_id,
                    &non_null_expr.expression,
                    node_id,
                    flags,
                );
                // Remove `null` and `undefined` from the type
                // TODO(correctness): instead of just directly evaluating, we should map to
                // the `NonNullable<T>` type and then evaluate that
                self.remove_null_or_undefined(ty)
            }
            Expression::NewExpression(new_expression) => {
                self.get_type_of_new_expression(program_id, new_expression)
            }
            Expression::CallExpression(call_expression) => {
                self.get_type_of_call_expression(program_id, call_expression, node_id)
            }
            Expression::ArrayExpression(array_expression) => {
                self.get_type_of_array_expression(program_id, array_expression, node_id)
            }
            Expression::ComputedMemberExpression(member) => {
                self.get_type_of_computed_member_expression(program_id, member, node_id)
            }
            Expression::StaticMemberExpression(member) => {
                self.get_type_of_static_member_expression(program_id, member, node_id)
            }
            Expression::ParenthesizedExpression(parenthesized) => self
                .get_type_of_expression_with_node(
                    program_id,
                    &parenthesized.expression,
                    node_id,
                    GetTypeFlags::NONE,
                ),
            Expression::TSTypeAssertion(assertion) => {
                self.get_type_from_type_assertion(program_id, &assertion.type_annotation)
            }
            Expression::TSAsExpression(assertion) => {
                self.get_type_from_type_assertion(program_id, &assertion.type_annotation)
            }
            Expression::ThisExpression(_) => node_id
                .and_then(|node_id| self.get_enclosing_class_instance_type(program_id, node_id))
                .unwrap_or_else(Ty::any),
            Expression::FunctionExpression(function) => self
                .get_type_of_function_signature_with_node(
                    program_id,
                    FunctionKind::Function(function),
                    node_id,
                ),
            Expression::ArrowFunctionExpression(arrow_function) => self
                .get_type_of_function_signature_with_node(
                    program_id,
                    FunctionKind::ArrowFunction(arrow_function),
                    node_id,
                ),
            Expression::NullLiteral(_) => Ty::null(),
            Expression::AwaitExpression(await_expr) => {
                self.get_type_of_await_expression(program_id, await_expr, node_id)
            }
            Expression::NumericLiteral(literal) => {
                if flags.preserve_literals() {
                    Ty::number_literal(self.arena(), self.arena().str(&literal.raw_str()))
                } else {
                    Ty::number()
                }
            }
            Expression::StringLiteral(literal) => {
                if flags.preserve_literals() {
                    Ty::string_literal(self.arena(), self.get_string_literal_value(literal))
                } else {
                    Ty::string()
                }
            }
            Expression::BooleanLiteral(literal) => {
                if flags.preserve_literals() {
                    Ty::boolean_literal(literal.value)
                } else {
                    Ty::boolean()
                }
            }
            Expression::BigIntLiteral(literal) => {
                if flags.preserve_literals() {
                    Ty::bigint_literal(self.arena(), self.get_bigint_literal_value(literal))
                } else {
                    Ty::bigint()
                }
            }
            Expression::TemplateLiteral(literal) => {
                if flags.preserve_literals() {
                    if literal.expressions.is_empty()
                        && let Some(quasi) = literal.single_quasi()
                    {
                        Ty::string_literal(self.arena(), quasi.as_str())
                    } else {
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
                    }
                } else {
                    Ty::string()
                }
            }
            // TODO(correctness): Handle all of these cases.
            Expression::RegExpLiteral(_) => Ty::any(),
            Expression::MetaProperty(_) => Ty::any(),
            Expression::Super(_) => Ty::any(),
            Expression::ChainExpression(_) => Ty::any(),
            Expression::ClassExpression(_) => Ty::any(),
            Expression::ImportExpression(_) => Ty::any(),
            Expression::LogicalExpression(_) => Ty::any(),
            Expression::SequenceExpression(_) => Ty::any(),
            Expression::TaggedTemplateExpression(_) => Ty::any(),
            Expression::UpdateExpression(_) => Ty::any(),
            Expression::YieldExpression(_) => Ty::any(),
            Expression::PrivateInExpression(_) => Ty::any(),
            Expression::JSXElement(_) => Ty::any(),
            Expression::JSXFragment(_) => Ty::any(),
            Expression::TSSatisfiesExpression(_) => Ty::any(),
            Expression::TSInstantiationExpression(_) => Ty::any(),
            Expression::V8IntrinsicExpression(_) => Ty::any(),
            Expression::PrivateFieldExpression(_) => Ty::any(),
        }
    }

    fn identifier_node_ref(
        &self,
        program_id: program::ProgramId,
        identifier: &IdentifierReference<'a>,
    ) -> NodeRef {
        NodeRef::new(program_id, identifier.node_id())
    }

    fn is_in_exported_declaration(&self, program_id: program::ProgramId, node_id: NodeId) -> bool {
        self.nodes(program_id).ancestor_kinds(node_id).any(|kind| {
            matches!(
                kind,
                AstKind::ExportNamedDeclaration(_)
                    | AstKind::ExportDefaultDeclaration(_)
                    | AstKind::ExportAllDeclaration(_)
            )
        })
    }

    /// Removes `null` and `undefined` from the type, like when using `!` or `NonNullable<T>`.
    pub(crate) fn remove_null_or_undefined(&self, ty: Ty<'a>) -> Ty<'a> {
        match ty {
            Ty::Null => Ty::never(),
            Ty::Undefined => Ty::never(),
            Ty::Union(union) => Ty::union(
                self.arena(),
                union.types.iter().filter_map(|t| {
                    let t = self.remove_null_or_undefined(*t);
                    if t.is_never() { None } else { Some(t) }
                }),
            ),
            _ => ty,
        }
    }

    pub(crate) fn get_string_literal_value(&self, literal: &StringLiteral<'a>) -> &'a str {
        literal.raw.as_ref().map_or_else(
            || self.arena().str(&format!("{:?}", literal.value.as_str())),
            |raw| raw.as_str(),
        )
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
        program_id: program::ProgramId,
        binary_expression: &'a BinaryExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let left = self.get_type_of_expression_with_node(
            program_id,
            &binary_expression.left,
            node_id,
            GetTypeFlags::NONE,
        );
        let right = self.get_type_of_expression_with_node(
            program_id,
            &binary_expression.right,
            node_id,
            GetTypeFlags::NONE,
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
        program_id: program::ProgramId,
        assignment_expression: &'a AssignmentExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let right = self.get_type_of_expression_with_node(
            program_id,
            &assignment_expression.right,
            node_id,
            GetTypeFlags::NONE,
        );
        match assignment_expression.operator {
            AssignmentOperator::Assign => right,
            AssignmentOperator::Addition => {
                if self.is_string_like_for_addition(right) {
                    Ty::string()
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
            // TODO(correctness): assume the correct type for logical assignment expressions
            AssignmentOperator::LogicalOr => Ty::any(),
            AssignmentOperator::LogicalAnd => Ty::any(),
            AssignmentOperator::LogicalNullish => Ty::any(),
        }
    }

    fn get_type_of_conditional_expression(
        &self,
        program_id: program::ProgramId,
        conditional: &'a ConditionalExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let consequent = self.get_type_of_expression_with_node(
            program_id,
            &conditional.consequent,
            node_id,
            GetTypeFlags::NONE,
        );
        let alternate = self.get_type_of_expression_with_node(
            program_id,
            &conditional.alternate,
            node_id,
            GetTypeFlags::NONE,
        );

        Ty::union(self.arena(), [consequent, alternate])
    }

    fn is_string_like_for_addition(&self, ty: Ty<'a>) -> bool {
        matches!(ty, Ty::String | Ty::StringLiteral(_))
    }

    /// Resolve a TypeScript type annotation, if any.
    fn get_type_from_ts_type_annotation(
        &self,
        program_id: program::ProgramId,
        type_annotation: Option<&'a TSTypeAnnotation<'a>>,
    ) -> Ty<'a> {
        type_annotation.map_or_else(Ty::any, |type_annotation| {
            self.get_type_from_ts_type(program_id, &type_annotation.type_annotation)
        })
    }

    fn get_type_from_property_signature_annotation(
        &self,
        program_id: program::ProgramId,
        type_annotation: &'a TSTypeAnnotation<'a>,
    ) -> Ty<'a> {
        if let TSType::TSTypeReference(reference) = &type_annotation.type_annotation
            && let Some(expanded) =
                self.get_flat_mapped_intersection_alias_reference(program_id, reference, 0)
        {
            return expanded;
        }

        let ty = self.get_type_from_ts_type(program_id, &type_annotation.type_annotation);
        self.get_apparent_property_signature_type(program_id, ty, 0)
    }

    fn get_apparent_property_signature_type(
        &self,
        program_id: program::ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match ty {
            Ty::TypeReference(reference)
                if self.is_conditional_type_alias_reference(program_id, reference) =>
            {
                self.get_conditional_type_alias_reference_type(program_id, reference)
                    .map(|(expanded_program_id, expanded)| {
                        let expanded = if matches!(expanded, Ty::Conditional(_)) {
                            self.apparent_type_for_conditional_match(
                                expanded_program_id,
                                expanded,
                                depth + 1,
                            )
                        } else {
                            expanded
                        };
                        if matches!(expanded, Ty::Conditional(_)) {
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
            Ty::Union(union) => Ty::union(
                self.arena(),
                union.types.iter().map(|ty| {
                    self.get_apparent_property_signature_type(program_id, *ty, depth + 1)
                }),
            ),
            _ => ty,
        }
    }

    /// Resolve a TypeScript type node, using symbols for references that need checker state.
    fn get_type_from_ts_type(&self, program_id: program::ProgramId, ty: &'a TSType<'a>) -> Ty<'a> {
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
            TSType::TSTypeLiteral(type_literal) => Ty::object_with_signatures(
                self.arena(),
                type_literal
                    .members
                    .iter()
                    .filter_map(|member| match member {
                        TSSignature::TSPropertySignature(property) => {
                            let name = property_key_name_str(&property.key)?;
                            let ty = self.get_type_from_ts_type_annotation(
                                program_id,
                                property.type_annotation.as_deref(),
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
                            let name = property_key_name_str(&method.key)?;
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
            TSType::TSTemplateLiteralType(template_literal) => Ty::template_literal(
                self.arena(),
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
                    let name = numeric_literal.raw.as_ref().map_or_else(
                        || self.arena().str(&numeric_literal.value.to_string()),
                        |raw| raw.as_str(),
                    );
                    Ty::number_literal(self.arena(), name)
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
                    Ty::template_literal(self.arena(), quasis, expressions)
                }
                TSLiteral::UnaryExpression(_) => Ty::none(),
            },
            TSType::TSTupleType(tuple_type) => Ty::tuple(
                self.arena(),
                tuple_type
                    .element_types
                    .iter()
                    .map(|ty| match ty {
                        TSTupleElement::TSRestType(rest) => TupleElement::Rest(
                            self.get_type_from_ts_type(program_id, &rest.type_annotation),
                        ),
                        TSTupleElement::TSOptionalType(optional) => {
                            TupleElement::Optional(Ty::union(
                                self.arena(),
                                [
                                    self.get_type_from_ts_type(
                                        program_id,
                                        &optional.type_annotation,
                                    ),
                                    Ty::undefined(),
                                ],
                            ))
                        }
                        _ => TupleElement::Regular(match ty.as_ts_type() {
                            Some(ts_type) => self.get_type_from_ts_type(program_id, ts_type),
                            None => Ty::none(),
                        }),
                    })
                    .collect(),
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
                    match self.get_type_from_ts_type(program_id, &operator.type_annotation) {
                        Ty::Array(array) => Ty::readonly_array(self.arena(), array.element_type),
                        Ty::Tuple(tuple) => Ty::readonly_tuple(
                            self.arena(),
                            tuple.elements.iter().copied().collect(),
                        ),
                        inner => inner,
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
                self.resolve_indexed_access_type(program_id, object_type, lookup_index_type)
                    .unwrap_or_else(|| Ty::indexed_access(self.arena(), object_type, index_type))
            }
            TSType::TSConditionalType(conditional) => {
                let check_type = self.get_type_from_ts_type(program_id, &conditional.check_type);
                let contains_infer = ts_type_contains_infer(&conditional.extends_type);
                let extends_type = if contains_infer {
                    self.get_type_from_ts_type_expanding_top_level_aliases(
                        program_id,
                        &conditional.extends_type,
                    )
                } else {
                    self.get_type_from_ts_type(program_id, &conditional.extends_type)
                };
                let check_type = if contains_infer {
                    self.apparent_type_for_conditional_match(program_id, check_type, 0)
                } else {
                    check_type
                };
                Ty::conditional(
                    self.arena(),
                    check_type,
                    extends_type,
                    self.get_type_from_ts_type(program_id, &conditional.true_type),
                    self.get_type_from_ts_type(program_id, &conditional.false_type),
                    matches!(
                        conditional.check_type,
                        TSType::TSTypeReference(ref reference) if reference.type_arguments.is_none()
                    ),
                )
            }
            TSType::TSInferType(infer) => Ty::infer(
                self.arena(),
                self.type_parameter_from_ts_type_parameter(program_id, &infer.type_parameter),
            ),
            TSType::TSMappedType(mapped) => self.get_type_from_ts_mapped_type(program_id, mapped),
            TSType::TSTypePredicate(predicate) => type_predicate_return_type(predicate.asserts),
            TSType::TSIntrinsicKeyword(_) => {
                // TODO(correctness): handle intrinsic keywords
                Ty::none()
            }
            TSType::TSConstructorType(_) => {
                // TODO(correctness): handle constructor types
                Ty::none()
            }
            TSType::TSImportType(_) => {
                // TODO(correctness): handle types like `import('foo').T`
                Ty::none()
            }
            TSType::TSNamedTupleMember(_) => {
                // TODO(correctness): handle named tuple members
                Ty::none()
            }
            TSType::JSDocNullableType(_)
            | TSType::JSDocNonNullableType(_)
            | TSType::JSDocUnknownType(_) => {
                // TODO(completeness): We are not currently handling JSDoc.
                Ty::any()
            }
        }
    }

    fn get_type_from_ts_mapped_type(
        &self,
        program_id: program::ProgramId,
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
            Ty::union(self.arena(), [template, Ty::undefined()])
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
        program_id: program::ProgramId,
        query: &'a TSTypeQuery<'a>,
    ) -> Ty<'a> {
        let Some(name) = ts_type_query_expr_name_to_str(self.arena(), &query.expr_name) else {
            return Ty::any();
        };

        let resolved = match &query.expr_name {
            TSTypeQueryExprName::IdentifierReference(identifier) => identifier
                .reference_id
                .get()
                .and_then(|reference_id| {
                    self.semantic(program_id)
                        .scoping()
                        .get_reference(reference_id)
                        .symbol_id()
                })
                .map(|symbol_id| self.get_type_of_symbol(SymbolRef::new(program_id, symbol_id)))
                .or_else(|| {
                    self.get_value_symbol_for_name(program_id, name)
                        .map(|symbol| self.get_type_of_symbol(symbol))
                })
                .unwrap_or_else(Ty::any),
            // TODO(correctness): resolve qualified-name and `this` typeof targets to a
            // real symbol so `resolved` is meaningful instead of `Ty::any`.
            _ => Ty::any(),
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
        program_id: program::ProgramId,
        alias: &'a oxc_ast::ast::TSTypeAliasDeclaration<'a>,
    ) -> Ty<'a> {
        if let TSType::TSTypeQuery(query) = &alias.type_annotation
            && let Some(name) = ts_type_query_expr_name_to_str(self.arena(), &query.expr_name)
        {
            let query_type = self.get_type_from_ts_type_query(program_id, query);
            if let Ty::TypeQuery(query) = query_type
                && matches!(query.resolved, Ty::UniqueSymbol(_))
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
            return Ty::type_query(self.arena(), name, Ty::any(), type_arguments);
        }

        let ty = self
            .get_type_from_ts_type_expanding_top_level_aliases(program_id, &alias.type_annotation);
        self.expand_index_signature_alias_result(program_id, ty, 0)
    }

    fn get_type_from_ts_type_expanding_top_level_aliases(
        &self,
        program_id: program::ProgramId,
        ty: &'a TSType<'a>,
    ) -> Ty<'a> {
        self.get_type_from_ts_type_expanding_top_level_aliases_at_depth(program_id, ty, 0)
    }

    fn get_type_from_ts_type_expanding_top_level_aliases_at_depth(
        &self,
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match ty {
            Ty::TypeReference(reference) => self
                .get_expanded_type_alias_reference_type(program_id, reference, depth + 1)
                .map(|(_, expanded)| expanded)
                .filter(|expanded| expanded.is_index_signature_object())
                .unwrap_or(ty),
            _ => ty,
        }
    }

    fn resolve_indexed_access_type(
        &self,
        program_id: program::ProgramId,
        object_type: Ty<'a>,
        index_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        if let Ty::Array(array) = object_type
            && index_type.is_number_index_type()
        {
            return Some(array.element_type);
        }

        match index_type {
            Ty::Union(union) => {
                let property_types = union
                    .types
                    .iter()
                    .map(|index_type| {
                        self.resolve_indexed_access_type(program_id, object_type, *index_type)
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(Ty::union(self.arena(), property_types))
            }
            _ => {
                let property_name = index_type_to_property_name(self.arena(), index_type)?;
                self.get_property_type_for_indexed_access(program_id, object_type, property_name)
            }
        }
    }

    fn get_property_type_for_indexed_access(
        &self,
        program_id: program::ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        match object_type {
            Ty::Object(object) => object.properties.iter().find_map(|property| {
                if property.computed || property.name != property_name {
                    return None;
                }
                Some(if property.optional {
                    Ty::union(self.arena(), [property.ty, Ty::undefined()])
                } else {
                    property.ty
                })
            }),
            Ty::Union(union) => {
                let property_types = union
                    .types
                    .iter()
                    .map(|ty| {
                        self.get_property_type_for_indexed_access(program_id, *ty, property_name)
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(Ty::union(self.arena(), property_types))
            }
            Ty::Intersection(intersection) => intersection.types.iter().find_map(|ty| {
                self.get_property_type_for_indexed_access(program_id, *ty, property_name)
            }),
            Ty::TypeReference(reference) => self
                .get_expanded_type_alias_reference_type(program_id, reference, 0)
                .and_then(|(expanded_program_id, expanded)| {
                    self.get_property_type_for_indexed_access(
                        expanded_program_id,
                        expanded,
                        property_name,
                    )
                })
                .or_else(|| {
                    self.get_property_type_of_interface_type(program_id, reference, property_name)
                }),
            _ => None,
        }
    }

    fn expand_type_at_use(
        &self,
        program_id: program::ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match ty {
            Ty::TypeReference(reference)
                if self.is_global_awaited_type_reference(program_id, reference) =>
            {
                let target =
                    self.expand_type_at_use(program_id, reference.type_arguments[0], depth + 1);
                self.get_awaited_type(program_id, target)
            }
            Ty::TypeReference(reference) => self
                .get_expanded_type_alias_reference_type(program_id, reference, depth + 1)
                .map(|(expanded_program_id, expanded)| {
                    self.expand_type_at_use(expanded_program_id, expanded, depth + 1)
                })
                .unwrap_or(ty),
            Ty::IndexedAccess(indexed_access) => {
                let object_type =
                    self.expand_type_at_use(program_id, indexed_access.object_type, depth + 1);
                let index_type = indexed_access.index_type;
                let lookup_index_type =
                    self.expand_type_for_index_lookup(program_id, index_type, depth + 1);
                self.resolve_indexed_access_type(program_id, object_type, lookup_index_type)
                    .map(|resolved| self.expand_type_at_use(program_id, resolved, depth + 1))
                    .unwrap_or_else(|| Ty::indexed_access(self.arena(), object_type, index_type))
            }
            Ty::Mapped(mapped) => self
                .expand_mapped_type(program_id, mapped, depth + 1)
                .unwrap_or(ty),
            Ty::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.expand_type_at_use(program_id, *ty, depth + 1)),
            ),
            Ty::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection
                    .types
                    .iter()
                    .map(|ty| self.expand_type_at_use(program_id, *ty, depth + 1)),
            ),
            Ty::Conditional(conditional) => Ty::conditional(
                self.arena(),
                self.expand_type_at_use(program_id, conditional.check_type, depth + 1),
                self.expand_type_at_use(program_id, conditional.extends_type, depth + 1),
                self.expand_type_at_use(program_id, conditional.true_type, depth + 1),
                self.expand_type_at_use(program_id, conditional.false_type, depth + 1),
                conditional.is_distributive,
            ),
            Ty::Keyof(keyof) => Ty::keyof(
                self.arena(),
                self.expand_type_at_use(program_id, keyof.target, depth + 1),
            ),
            _ => ty,
        }
    }

    fn expand_type_for_index_lookup(
        &self,
        program_id: program::ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match ty {
            Ty::TypeReference(reference) => {
                let expanded_arguments = reference
                    .type_arguments
                    .iter()
                    .map(|ty| self.expand_type_for_index_lookup(program_id, *ty, depth + 1))
                    .collect::<Vec<_>>();
                let reference_ty = Ty::type_reference_with_explicit_type_argument_count(
                    self.arena(),
                    reference.name,
                    expanded_arguments,
                    reference.explicit_type_argument_count,
                );
                let Ty::TypeReference(reference) = reference_ty else {
                    return reference_ty;
                };
                self.get_expanded_type_alias_reference_type(program_id, reference, depth + 1)
                    .map(|(expanded_program_id, expanded)| {
                        self.expand_type_for_index_lookup(expanded_program_id, expanded, depth + 1)
                    })
                    .unwrap_or(reference_ty)
            }
            Ty::Conditional(conditional) => Ty::conditional(
                self.arena(),
                self.expand_type_for_index_lookup(program_id, conditional.check_type, depth + 1),
                self.expand_type_for_index_lookup(program_id, conditional.extends_type, depth + 1),
                self.expand_type_for_index_lookup(program_id, conditional.true_type, depth + 1),
                self.expand_type_for_index_lookup(program_id, conditional.false_type, depth + 1),
                conditional.is_distributive,
            ),
            Ty::Keyof(keyof) => Ty::keyof(
                self.arena(),
                self.expand_type_for_index_lookup(program_id, keyof.target, depth + 1),
            ),
            Ty::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.expand_type_for_index_lookup(program_id, *ty, depth + 1)),
            ),
            _ => ty,
        }
    }

    fn expand_mapped_type(
        &self,
        program_id: program::ProgramId,
        mapped: &TyMapped<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if let Some(ty) = self.expand_array_mapped_type(program_id, mapped, depth + 1) {
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
            let substitutions = HashMap::from([(mapped.key, key_type)]);
            let property_name = if let Some(name_type) = mapped.name_type {
                let name_type = name_type.substitute_type_parameters(self.arena(), &substitutions);
                let name_type = self.expand_type_at_use(program_id, name_type, depth + 1);
                if name_type.is_never() {
                    continue;
                }
                index_type_to_property_name(self.arena(), name_type)?
            } else {
                property.name
            };
            let ty = mapped
                .template
                .substitute_type_parameters(self.arena(), &substitutions);
            let ty = self.expand_type_at_use(program_id, ty, depth + 1);
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

    fn expand_array_mapped_type(
        &self,
        program_id: program::ProgramId,
        mapped: &TyMapped<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        let Ty::Keyof(keyof) = mapped.constraint else {
            return None;
        };
        let Ty::Array(_) = self.expand_type_at_use(program_id, keyof.target, depth + 1) else {
            return None;
        };
        if mapped.name_type.is_some() {
            return None;
        }

        let substitutions = HashMap::from([(mapped.key, Ty::number())]);
        let element_type = mapped
            .template
            .substitute_type_parameters(self.arena(), &substitutions);
        let element_type = self.expand_type_at_use(program_id, element_type, depth + 1);
        Some(Ty::array(self.arena(), element_type))
    }

    fn expand_index_signature_mapped_type(
        &self,
        program_id: program::ProgramId,
        mapped: &TyMapped<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if mapped.name_type.is_some() {
            return None;
        }

        let key_types = index_signature_key_types(mapped.constraint)?;
        let index_infos = key_types.into_iter().map(|key_type| {
            let substitutions = HashMap::from([(mapped.key, key_type)]);
            let ty = mapped
                .template
                .substitute_type_parameters(self.arena(), &substitutions);
            let ty = self.expand_type_at_use(program_id, ty, depth + 1);
            IndexInfo {
                key_type,
                value_type: ty,
                readonly: matches!(mapped.readonly, MappedModifier::True | MappedModifier::Plus),
            }
        });

        Some(Ty::object_with_index_infos(self.arena(), [], index_infos))
    }

    fn properties_for_mapped_constraint(
        &self,
        program_id: program::ProgramId,
        constraint: Ty<'a>,
        depth: usize,
    ) -> Option<Vec<TyProperty<'a>>> {
        let Ty::Keyof(keyof) = constraint else {
            return None;
        };
        self.properties_for_keyof_type(program_id, keyof.target, depth + 1)
    }

    fn properties_for_keyof_type(
        &self,
        program_id: program::ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Option<Vec<TyProperty<'a>>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }

        match self.expand_type_at_use(program_id, ty, depth + 1) {
            Ty::Object(object) => Some(
                object
                    .properties
                    .iter()
                    .copied()
                    .filter(|property| !property.computed)
                    .collect(),
            ),
            Ty::Intersection(intersection) => {
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
            Ty::TypeReference(reference) => self
                .get_expanded_type_alias_reference_type(program_id, reference, depth + 1)
                .and_then(|(expanded_program_id, expanded)| {
                    self.properties_for_keyof_type(expanded_program_id, expanded, depth + 1)
                }),
            _ => None,
        }
    }

    fn get_expanded_type_alias_reference(
        &self,
        program_id: program::ProgramId,
        reference: &'a TSTypeReference<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        let name = ts_type_name_to_str(self.arena(), &reference.type_name);
        let mut type_arguments = self.type_arguments_from_reference(program_id, reference);

        self.fill_default_type_arguments(program_id, name, &mut type_arguments);

        let symbol = self.get_type_symbol_for_name(program_id, name)?;
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.get_expanded_type_alias_declaration(
            symbol.program_id,
            declaration,
            &type_arguments,
            depth,
        )
    }

    fn get_flat_mapped_intersection_alias_reference(
        &self,
        program_id: program::ProgramId,
        reference: &'a TSTypeReference<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }

        let name = ts_type_name_to_str(self.arena(), &reference.type_name);
        let mut type_arguments = self.type_arguments_from_reference(program_id, reference);

        self.fill_default_type_arguments(program_id, name, &mut type_arguments);

        let symbol = self.get_type_symbol_for_name(program_id, name)?;
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.get_flat_mapped_intersection_alias_declaration(
            symbol.program_id,
            declaration,
            &type_arguments,
            depth + 1,
        )
    }

    fn get_flat_mapped_intersection_alias_declaration(
        &self,
        program_id: program::ProgramId,
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
                let ty = self
                    .get_type_from_ts_type_expanding_top_level_aliases_at_depth(
                        program_id,
                        &alias.type_annotation,
                        depth + 1,
                    )
                    .substitute_type_parameters(self.arena(), &substitutions);
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
        program_id: program::ProgramId,
        declaration: NodeId,
        type_arguments: &[Ty<'a>],
        depth: usize,
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias)
                if !matches!(alias.type_annotation, TSType::TSTypeQuery(_)) =>
            {
                let substitutions = self.type_parameter_substitutions_for_type_arguments(
                    program_id,
                    alias.type_parameters.as_deref(),
                    type_arguments,
                );
                let ty = self
                    .get_type_from_ts_type_expanding_top_level_aliases_at_depth(
                        program_id,
                        &alias.type_annotation,
                        depth + 1,
                    )
                    .substitute_type_parameters(self.arena(), &substitutions);
                Some(self.expand_type_at_use(program_id, ty, depth + 1))
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

    /// Instantiate the pieces of a type-query result that accept explicit type arguments.
    fn instantiate_type_query_type(
        &self,
        program_id: program::ProgramId,
        ty: Ty<'a>,
        type_arguments: &[Ty<'a>],
    ) -> Ty<'a> {
        match ty {
            Ty::Intersection(intersection) => Ty::intersection(
                self.arena(),
                intersection
                    .types
                    .iter()
                    .map(|ty| self.instantiate_type_query_type(program_id, *ty, type_arguments)),
            ),
            Ty::Function(function) => self.instantiate_function_type(function, type_arguments),
            Ty::TypeQuery(query) if query.type_arguments.is_empty() => self
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
        let substitutions = function
            .type_parameters
            .iter()
            .zip(type_arguments.iter())
            .map(|(type_parameter, type_argument)| (type_parameter.name, *type_argument))
            .collect::<HashMap<_, _>>();
        let remaining_type_parameters = function
            .type_parameters
            .iter()
            .skip(type_arguments.len())
            .copied();

        Ty::function_with_type_predicate(
            self.arena(),
            remaining_type_parameters,
            function.parameters.iter().map(|parameter| {
                let ty = parameter
                    .ty
                    .substitute_type_parameters(self.arena(), &substitutions);
                if parameter.rest {
                    Ty::rest_parameter(parameter.name, ty)
                } else if parameter.optional {
                    Ty::optional_parameter(parameter.name, ty)
                } else {
                    Ty::parameter(parameter.name, ty)
                }
            }),
            function
                .return_type
                .substitute_type_parameters(self.arena(), &substitutions),
            function.type_predicate.map(|predicate| {
                predicate.substitute_type_parameters(self.arena(), &substitutions)
            }),
        )
    }

    /// Instantiate `typeof Class<T>` into the constructor/prototype shape TypeScript reports.
    fn instantiate_typeof_class_type(
        &self,
        program_id: program::ProgramId,
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

    fn get_type_from_ts_type_reference(
        &self,
        program_id: program::ProgramId,
        reference: &'a TSTypeReference<'a>,
    ) -> Ty<'a> {
        self.get_type_from_ts_type_reference_with_default_display(program_id, reference, false)
    }

    fn get_type_from_type_assertion(
        &self,
        program_id: program::ProgramId,
        ty: &'a TSType<'a>,
    ) -> Ty<'a> {
        match ty {
            TSType::TSTypeReference(reference) => self
                .get_type_from_ts_type_reference_with_default_display(program_id, reference, true),
            _ => self.get_type_from_ts_type(program_id, ty),
        }
    }

    fn get_type_from_ts_type_reference_with_default_display(
        &self,
        program_id: program::ProgramId,
        reference: &'a TSTypeReference<'a>,
        display_default_type_arguments: bool,
    ) -> Ty<'a> {
        let name = ts_type_name_to_str(self.arena(), &reference.type_name);
        let mut type_arguments = self.type_arguments_from_reference(program_id, reference);
        let explicit_type_argument_count = type_arguments.len();

        self.fill_default_type_arguments(program_id, name, &mut type_arguments);
        let type_argument_display_count = if display_default_type_arguments {
            type_arguments.len()
        } else {
            explicit_type_argument_count
        };

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

        Ty::type_reference_with_explicit_type_argument_count(
            self.arena(),
            name,
            type_arguments.iter().copied(),
            type_argument_display_count,
        )
    }

    fn type_arguments_from_reference(
        &self,
        program_id: program::ProgramId,
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

    fn get_type_argument_from_ts_type(
        &self,
        program_id: program::ProgramId,
        ty: &'a TSType<'a>,
    ) -> Ty<'a> {
        match self.get_type_from_ts_type(program_id, ty) {
            Ty::TypeQuery(query) if query.type_arguments.is_empty() && !query.resolved.is_any() => {
                query.resolved
            }
            ty => self.get_apparent_type_at_use(program_id, ty, 0),
        }
    }

    fn apparent_type_for_conditional_match(
        &self,
        program_id: program::ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match ty {
            Ty::TypeReference(reference) => self
                .apparent_type_reference_for_conditional_match(program_id, reference, depth + 1)
                .unwrap_or(ty),
            Ty::Array(array) => {
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
            Ty::Tuple(tuple) => {
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
                if tuple.readonly {
                    Ty::readonly_tuple(self.arena(), elements)
                } else {
                    Ty::tuple(self.arena(), elements)
                }
            }
            Ty::Union(union) => Ty::r#union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.apparent_type_for_conditional_match(program_id, *ty, depth + 1)),
            ),
            Ty::Intersection(intersection) => Ty::intersection(
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
        program_id: program::ProgramId,
        reference: &TyTypeReference<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        let symbol = self.get_type_symbol_for_name(program_id, reference.name)?;
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.apparent_type_declaration_for_conditional_match(
            symbol.program_id,
            declaration,
            reference,
            depth,
        )
    }

    fn apparent_type_declaration_for_conditional_match(
        &self,
        program_id: program::ProgramId,
        declaration: NodeId,
        reference: &TyTypeReference<'a>,
        depth: usize,
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSInterfaceDeclaration(_) => {
                self.apparent_interface_type_for_conditional_match(reference)
            }
            AstKind::TSTypeAliasDeclaration(alias) => {
                let substitutions = self.type_parameter_substitutions_for_reference(
                    program_id,
                    alias.type_parameters.as_deref(),
                    reference,
                );
                let ty = self
                    .get_type_from_ts_type(program_id, &alias.type_annotation)
                    .substitute_type_parameters(self.arena(), &substitutions);
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
        reference: &TyTypeReference<'a>,
    ) -> Option<Ty<'a>> {
        let declarations = self.interface_declarations_for_name(reference.name);
        if declarations.is_empty() {
            return None;
        }

        let mut properties = Vec::new();
        let mut signatures = Vec::new();

        for &(program_id, interface) in declarations {
            let substitutions = self.type_parameter_substitutions_for_reference(
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
                        let ty = ty.substitute_type_parameters(self.arena(), &substitutions);
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
                        let signature = self.signature_from_function_parts(
                            program_id,
                            SignatureKind::Call,
                            method.type_parameters.as_deref(),
                            method.params.as_ref(),
                            method.return_type.as_deref(),
                        );
                        let signature =
                            signature.substitute_type_parameters(self.arena(), &substitutions);
                        properties.push(TyProperty {
                            name,
                            ty: Ty::Function(signature.function),
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
                        signatures.push(
                            signature.substitute_type_parameters(self.arena(), &substitutions),
                        );
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
        program_id: program::ProgramId,
        type_name: &str,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        let symbol = self.get_type_symbol_for_name(program_id, type_name)?;
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.get_expanded_type_query_alias_declaration(
            symbol.program_id,
            declaration,
            type_arguments,
        )
    }

    /// Resolve a type-query alias declaration and substitute the alias type arguments.
    fn get_expanded_type_query_alias_declaration(
        &self,
        program_id: program::ProgramId,
        declaration: NodeId,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias)
                if matches!(alias.type_annotation, TSType::TSTypeQuery(_)) =>
            {
                let type_parameters = self
                    .type_parameters_from_declaration(program_id, alias.type_parameters.as_deref());
                let substitutions = type_parameters
                    .iter()
                    .zip(type_arguments.iter())
                    .map(|(type_parameter, type_argument)| (type_parameter.name, *type_argument))
                    .collect::<HashMap<_, _>>();
                Some(
                    self.get_type_from_ts_type(program_id, &alias.type_annotation)
                        .substitute_type_parameters(self.arena(), &substitutions),
                )
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
        program_id: program::ProgramId,
        type_name: &str,
        type_arguments: &mut Vec<Ty<'a>>,
    ) {
        let Some(type_parameters) = self.get_type_parameters_for_type(program_id, type_name) else {
            return;
        };
        if type_arguments.len() >= type_parameters.len() {
            return;
        }

        let mut substitutions = HashMap::new();
        for (type_parameter, type_argument) in type_parameters.iter().zip(type_arguments.iter()) {
            substitutions.insert(type_parameter.name, *type_argument);
        }

        for type_parameter in type_parameters.iter().skip(type_arguments.len()) {
            let Some(default_type) = type_parameter.default_type else {
                break;
            };
            let default_type = default_type.substitute_type_parameters(
                self.arena(),
                &self.substitutions_with_unresolved_type_parameters_as_any(
                    &type_parameters,
                    &substitutions,
                ),
            );
            substitutions.insert(type_parameter.name, default_type);
            type_arguments.push(default_type);
        }
    }

    /// Return the instance type for the nearest enclosing class.
    /// This provides a class-backed type for `this` inside methods and field initializers.
    fn get_enclosing_class_instance_type(
        &self,
        program_id: program::ProgramId,
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

    fn get_type_of_object_expression(
        &self,
        program_id: program::ProgramId,
        object: &'a ObjectExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        Ty::object(
            self.arena(),
            object.properties.iter().filter_map(|property| {
                let ObjectPropertyKind::ObjectProperty(property) = property else {
                    return None;
                };
                let name = property_key_name_str(&property.key)?;
                let ty = self.get_type_of_expression_with_node(
                    program_id,
                    &property.value,
                    node_id,
                    GetTypeFlags::NONE,
                );
                Some(Ty::property(name, ty))
            }),
        )
    }

    fn get_type_of_static_member_expression(
        &self,
        program_id: program::ProgramId,
        member: &'a StaticMemberExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let object_type = self.get_type_of_expression_with_node(
            program_id,
            &member.object,
            node_id,
            GetTypeFlags::NONE,
        );
        let apparent_object_type = self.get_apparent_type_at_use(program_id, object_type, 0);
        let property_name = member.property.name.as_str();
        let ty = object_type
            .property_type(property_name)
            .or_else(|| apparent_object_type.property_type(property_name))
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
            .or_else(|| {
                if matches!(member.object, Expression::ThisExpression(_)) {
                    node_id
                        .and_then(|node_id| {
                            self.get_enclosing_class_instance_type(program_id, node_id)
                        })
                        .and_then(|this_type| {
                            self.get_property_type_of_named_type(
                                program_id,
                                &this_type,
                                property_name,
                            )
                        })
                } else {
                    None
                }
            })
            .unwrap_or_else(Ty::any);
        if matches!(ty, Ty::Function(_)) {
            ty
        } else {
            self.get_apparent_type_at_use(program_id, ty, 0)
        }
    }

    fn get_type_of_computed_member_expression(
        &self,
        program_id: program::ProgramId,
        member: &'a ComputedMemberExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let object_type = self.get_type_of_expression_with_node(
            program_id,
            &member.object,
            node_id,
            GetTypeFlags::NONE,
        );
        let Some(index) = tuple_index_from_expression(&member.expression) else {
            return Ty::any();
        };
        tuple_element_type_at_index(&object_type, index).unwrap_or_else(Ty::any)
    }

    fn get_property_type_of_global_interface_type(
        &self,
        program_id: program::ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let interface_type = match object_type {
            Ty::Array(array) if array.readonly => {
                self.get_global_readonly_array_type(program_id, array.element_type)
            }
            Ty::Array(array) => self.get_global_array_type(program_id, array.element_type),
            Ty::Object(_) | Ty::PrimitiveObject => self.get_global_object_type(program_id),
            Ty::Function(_) => self.get_global_function_type(program_id),
            Ty::String | Ty::StringLiteral(_) => self.get_global_string_type(program_id),
            Ty::Boolean | Ty::BooleanLiteral(_) => self.get_global_boolean_type(program_id),
            Ty::Number | Ty::NumberLiteral(_) => self.get_global_number_type(program_id),
            Ty::Symbol | Ty::UniqueSymbol(_) => self.get_global_symbol_type(program_id),
            Ty::Bigint | Ty::BigIntLiteral(_) => self.get_global_bigint_type(program_id),
            _ => return None,
        };
        let Some(Ty::TypeReference(reference)) = interface_type else {
            return None;
        };
        self.get_property_type_of_interface_type(program_id, reference, property_name)
    }

    fn is_in_contextually_typed_initializer(
        &self,
        program_id: program::ProgramId,
        node_id: NodeId,
    ) -> bool {
        self.nodes(program_id)
            .ancestors(node_id)
            .any(|node| match node.kind() {
                AstKind::VariableDeclarator(declarator) => declarator.type_annotation.is_some(),
                AstKind::PropertyDefinition(property) => property.type_annotation.is_some(),
                _ => false,
            })
    }

    fn get_type_of_call_expression(
        &self,
        program_id: program::ProgramId,
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
            return Ty::any();
        }

        // TODO(overloads): TypeScript Go's `checker.go` ranks candidates with a more nuanced
        // specificity pass. This first pass preserves declaration order and picks the first
        // arity/assignability-compatible signature.
        candidates
            .iter()
            .find_map(|signature| {
                self.resolve_call_signature_return_type(
                    program_id,
                    *signature,
                    call_expression,
                    node_id,
                    true,
                )
            })
            .or_else(|| {
                // TODO(overloads): mirror TypeScript Go's overload failure candidate diagnostics
                // instead of falling back to the first signature return type.
                candidates.first().and_then(|signature| {
                    self.resolve_call_signature_return_type(
                        program_id,
                        *signature,
                        call_expression,
                        node_id,
                        false,
                    )
                })
            })
            .unwrap_or_else(Ty::any)
    }

    fn get_signatures_of_type_in_program(
        &self,
        program_id: program::ProgramId,
        ty: Ty<'a>,
        kind: SignatureKind,
    ) -> Vec<Signature<'a>> {
        let signatures = self.get_signatures_of_type(ty, kind);
        if !signatures.is_empty() {
            return signatures;
        }

        let Ty::TypeReference(reference) = ty else {
            return signatures;
        };
        self.get_signatures_of_type_reference(program_id, reference, kind)
    }

    fn get_signatures_of_type_reference(
        &self,
        program_id: program::ProgramId,
        reference: &TyTypeReference<'a>,
        kind: SignatureKind,
    ) -> Vec<Signature<'a>> {
        let interface_signatures = self
            .interface_declarations_for_name(reference.name)
            .iter()
            .copied()
            .flat_map(|(program_id, interface)| {
                self.get_signatures_of_interface_declaration(program_id, interface, reference, kind)
            })
            .collect::<Vec<_>>();
        if !interface_signatures.is_empty() {
            return interface_signatures;
        }

        let Some(symbol) = self.get_type_symbol_for_name(program_id, reference.name) else {
            return Vec::new();
        };
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.get_signatures_of_type_declaration(symbol.program_id, declaration, reference, kind)
    }

    fn get_signatures_of_interface_declaration(
        &self,
        program_id: program::ProgramId,
        interface: &'a TSInterfaceDeclaration<'a>,
        reference: &TyTypeReference<'a>,
        kind: SignatureKind,
    ) -> Vec<Signature<'a>> {
        let substitutions = self.type_parameter_substitutions_for_reference(
            program_id,
            interface.type_parameters.as_deref(),
            reference,
        );
        interface
            .body
            .body
            .iter()
            .filter_map(|signature| self.signature_from_ts_signature(program_id, signature, kind))
            .map(|signature| signature.substitute_type_parameters(self.arena(), &substitutions))
            .collect()
    }

    fn get_signatures_of_type_declaration(
        &self,
        program_id: program::ProgramId,
        declaration: NodeId,
        reference: &TyTypeReference<'a>,
        kind: SignatureKind,
    ) -> Vec<Signature<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSInterfaceDeclaration(interface) => {
                self.get_signatures_of_interface_declaration(program_id, interface, reference, kind)
            }
            AstKind::TSTypeAliasDeclaration(alias) => self.get_signatures_of_type(
                self.get_type_from_ts_type(program_id, &alias.type_annotation)
                    .substitute_type_parameters(
                        self.arena(),
                        &self.type_parameter_substitutions_for_reference(
                            program_id,
                            alias.type_parameters.as_deref(),
                            reference,
                        ),
                    ),
                kind,
            ),
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_signatures_of_type_declaration(program_id, parent_id, reference, kind)
            }
            _ => Vec::new(),
        }
    }

    fn signature_from_ts_signature(
        &self,
        program_id: program::ProgramId,
        signature: &'a TSSignature<'a>,
        expected_kind: SignatureKind,
    ) -> Option<Signature<'a>> {
        let signature = match signature {
            TSSignature::TSCallSignatureDeclaration(signature)
                if expected_kind == SignatureKind::Call =>
            {
                self.signature_from_function_parts(
                    program_id,
                    SignatureKind::Call,
                    signature.type_parameters.as_deref(),
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
        program_id: program::ProgramId,
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

    fn signature_from_function_parts(
        &self,
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
        kind: SignatureKind,
        type_parameters: Option<&'a oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        this_param: Option<&'a TSThisParameter<'a>>,
        parameters: &'a FormalParameters<'a>,
        return_type: Option<&'a TSTypeAnnotation<'a>>,
    ) -> Signature<'a> {
        let parameters = self.function_type_parameters(program_id, this_param, parameters);
        let (return_type, type_predicate) = self.return_type_and_type_predicate_from_annotation(
            program_id,
            &parameters,
            return_type,
        );
        let Ty::Function(function) = Ty::function_with_type_predicate(
            self.arena(),
            self.type_parameters_from_declaration(program_id, type_parameters),
            parameters,
            return_type,
            type_predicate,
        ) else {
            unreachable!("signature construction always creates a function type")
        };
        Signature::new(kind, function)
    }

    fn return_type_and_type_predicate_from_annotation(
        &self,
        program_id: program::ProgramId,
        parameters: &[TyParameter<'a>],
        return_type: Option<&'a TSTypeAnnotation<'a>>,
    ) -> (Ty<'a>, Option<TyTypePredicate<'a>>) {
        return_type_and_type_predicate_from_annotation_with_resolver(
            parameters,
            return_type,
            |annotation| self.get_type_from_ts_type_annotation(program_id, Some(annotation)),
        )
    }

    fn resolve_call_signature_return_type(
        &self,
        program_id: program::ProgramId,
        signature: Signature<'a>,
        call_expression: &'a CallExpression<'a>,
        node_id: Option<NodeId>,
        require_applicable: bool,
    ) -> Option<Ty<'a>> {
        let substitutions = self.infer_call_type_parameter_substitutions(
            program_id,
            signature.function,
            call_expression,
            node_id,
        );
        let instantiated = signature
            .function
            .return_type
            .substitute_type_parameters(self.arena(), &substitutions);

        if require_applicable
            && !self.is_call_signature_applicable(
                program_id,
                signature.function,
                call_expression,
                node_id,
                &substitutions,
            )
        {
            return None;
        }

        Some(instantiated)
    }

    fn explicit_call_type_parameter_substitutions(
        &self,
        program_id: program::ProgramId,
        function: &'a TyFunction<'a>,
        call_expression: &'a CallExpression<'a>,
    ) -> HashMap<&'a str, Ty<'a>> {
        let (mut substitutions, _) = self.explicit_type_parameter_substitutions(
            program_id,
            function,
            call_expression.type_arguments.as_deref(),
        );
        self.add_type_parameter_fallback_substitutions(function, &mut substitutions, false);

        substitutions
    }

    pub(crate) fn explicit_type_parameter_substitutions(
        &self,
        program_id: program::ProgramId,
        function: &'a TyFunction<'a>,
        type_arguments: Option<&'a oxc_ast::ast::TSTypeParameterInstantiation<'a>>,
    ) -> (HashMap<&'a str, Ty<'a>>, Vec<&'a str>) {
        let mut substitutions = HashMap::new();
        let mut explicit_type_parameters = Vec::new();

        if let Some(type_arguments) = type_arguments {
            for (type_parameter, type_argument) in function
                .type_parameters
                .iter()
                .zip(type_arguments.params.iter())
            {
                substitutions.insert(
                    type_parameter.name,
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
        substitutions: &mut HashMap<&'a str, Ty<'a>>,
        fill_unresolved_with_unknown: bool,
    ) {
        for type_parameter in &function.type_parameters {
            if substitutions.contains_key(type_parameter.name) {
                continue;
            }
            if let Some(fallback_type) = type_parameter
                .default_type
                .or(type_parameter.constraint_type)
            {
                substitutions.insert(
                    type_parameter.name,
                    fallback_type.substitute_type_parameters(self.arena(), substitutions),
                );
            }
        }

        if fill_unresolved_with_unknown {
            for type_parameter in &function.type_parameters {
                substitutions
                    .entry(type_parameter.name)
                    .or_insert_with(Ty::unknown);
            }
        }
    }

    fn is_call_signature_applicable(
        &self,
        program_id: program::ProgramId,
        function: &TyFunction<'a>,
        call_expression: &'a CallExpression<'a>,
        node_id: Option<NodeId>,
        substitutions: &HashMap<&'a str, Ty<'a>>,
    ) -> bool {
        if !self.has_compatible_type_argument_count(
            function,
            call_expression
                .type_arguments
                .as_ref()
                .map_or(0, |type_arguments| type_arguments.params.len()),
        ) {
            return false;
        }
        if !self.has_compatible_argument_count(function, call_expression.arguments.len()) {
            return false;
        }

        self.arguments_are_assignable_to_parameters(
            program_id,
            function,
            call_expression
                .arguments
                .iter()
                .map(|argument| argument.as_expression()),
            node_id,
            substitutions,
        )
    }

    fn get_call_parameter_type_at(
        &self,
        function: &TyFunction<'a>,
        index: usize,
    ) -> Option<Ty<'a>> {
        let parameter = function
            .parameters
            .get(index)
            .or_else(|| function.parameters.iter().find(|parameter| parameter.rest))?;
        if parameter.rest {
            Some(parameter.ty.array_element_type().unwrap_or(parameter.ty))
        } else {
            Some(parameter.ty)
        }
    }

    fn get_type_of_new_expression(
        &self,
        program_id: program::ProgramId,
        new_expression: &'a NewExpression<'a>,
    ) -> Ty<'a> {
        let Expression::Identifier(identifier) = &new_expression.callee else {
            return Ty::any();
        };

        let constructor_type = identifier
            .reference_id
            .get()
            .and_then(|reference_id| {
                self.semantic(program_id)
                    .scoping()
                    .get_reference(reference_id)
                    .symbol_id()
            })
            .map(|symbol_id| SymbolRef::new(program_id, symbol_id))
            .or_else(|| self.get_value_symbol_for_name(program_id, identifier.name.as_str()))
            .map(|symbol| self.get_type_of_symbol(symbol));

        if let Some(Ty::TypeQuery(query)) = constructor_type
            && query.type_arguments.is_empty()
        {
            return Ty::type_reference(self.arena(), query.name, std::iter::empty());
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
        program_id: program::ProgramId,
        constructor_type: Ty<'a>,
        new_expression: &'a NewExpression<'a>,
    ) -> Option<Ty<'a>> {
        let candidates = self.get_signatures_of_type_in_program(
            program_id,
            constructor_type,
            SignatureKind::Construct,
        );
        candidates
            .iter()
            .find_map(|signature| {
                self.resolve_construct_signature_candidate(
                    program_id,
                    *signature,
                    new_expression,
                    true,
                )
            })
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
    }

    fn resolve_construct_signature_candidate(
        &self,
        program_id: program::ProgramId,
        signature: Signature<'a>,
        new_expression: &'a NewExpression<'a>,
        require_applicable: bool,
    ) -> Option<Ty<'a>> {
        let substitutions = self.infer_construct_type_parameter_substitutions(
            program_id,
            signature.function,
            new_expression,
        );

        if require_applicable
            && !self.is_construct_signature_applicable(
                program_id,
                signature.function,
                new_expression,
                &substitutions,
            )
        {
            return None;
        }

        Some(
            signature
                .function
                .return_type
                .substitute_type_parameters(self.arena(), &substitutions),
        )
    }

    fn explicit_construct_type_parameter_substitutions(
        &self,
        program_id: program::ProgramId,
        function: &'a TyFunction<'a>,
        new_expression: &'a NewExpression<'a>,
    ) -> HashMap<&'a str, Ty<'a>> {
        let (mut substitutions, _) = self.explicit_type_parameter_substitutions(
            program_id,
            function,
            new_expression.type_arguments.as_deref(),
        );
        self.add_type_parameter_fallback_substitutions(function, &mut substitutions, true);

        substitutions
    }

    fn is_construct_signature_applicable(
        &self,
        program_id: program::ProgramId,
        function: &TyFunction<'a>,
        new_expression: &'a NewExpression<'a>,
        substitutions: &HashMap<&'a str, Ty<'a>>,
    ) -> bool {
        if !self.has_compatible_type_argument_count(
            function,
            new_expression
                .type_arguments
                .as_ref()
                .map_or(0, |type_arguments| type_arguments.params.len()),
        ) {
            return false;
        }
        if !self.has_compatible_argument_count(function, new_expression.arguments.len()) {
            return false;
        }

        self.arguments_are_assignable_to_parameters(
            program_id,
            function,
            new_expression
                .arguments
                .iter()
                .map(|argument| argument.as_expression()),
            None,
            substitutions,
        )
    }

    fn has_compatible_type_argument_count(
        &self,
        function: &TyFunction<'a>,
        type_argument_count: usize,
    ) -> bool {
        type_argument_count <= function.type_parameters.len()
    }

    fn has_compatible_argument_count(
        &self,
        function: &TyFunction<'a>,
        argument_count: usize,
    ) -> bool {
        let minimum_argument_count = function
            .parameters
            .iter()
            .filter(|parameter| !parameter.optional && !parameter.rest)
            .count();
        let has_rest_parameter = function.parameters.iter().any(|parameter| parameter.rest);

        argument_count >= minimum_argument_count
            && (has_rest_parameter || argument_count <= function.parameters.len())
    }

    fn arguments_are_assignable_to_parameters(
        &self,
        program_id: program::ProgramId,
        function: &TyFunction<'a>,
        arguments: impl Iterator<Item = Option<&'a Expression<'a>>>,
        node_id: Option<NodeId>,
        substitutions: &HashMap<&'a str, Ty<'a>>,
    ) -> bool {
        for (index, argument) in arguments.enumerate() {
            let Some(argument) = argument else {
                continue;
            };
            let Some(parameter_type) = self.get_call_parameter_type_at(function, index) else {
                return false;
            };
            let parameter_type =
                parameter_type.substitute_type_parameters(self.arena(), substitutions);
            let argument_type = self.get_type_of_expression_with_node(
                program_id,
                argument,
                node_id,
                GetTypeFlags::NONE,
            );
            if !self.is_assignable_to(argument_type, parameter_type) {
                return false;
            }
        }

        true
    }

    fn get_property_type_of_named_type(
        &self,
        program_id: program::ProgramId,
        object_type: &Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let (class_name, is_static) = match object_type {
            Ty::TypeReference(reference) => {
                if let Some(ty) =
                    self.get_property_type_of_interface_type(program_id, reference, property_name)
                {
                    return Some(ty);
                }
                (reference.name, false)
            }
            // `typeof Class` value-side property access (statics).
            Ty::TypeQuery(query) => (query.name, true),
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
        program_id: program::ProgramId,
        reference: &TyTypeReference<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        if let Some(ty) = self.get_property_type_of_merged_interface_type(reference, property_name)
        {
            return Some(ty);
        }

        let symbol = self.get_type_symbol_for_name(program_id, reference.name)?;
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.get_property_type_of_interface_declaration(
            symbol.program_id,
            declaration,
            reference,
            property_name,
        )
    }

    fn get_property_type_of_merged_interface_type(
        &self,
        reference: &TyTypeReference<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let declarations = self.interface_declarations_for_name(reference.name);
        if declarations.is_empty() {
            return None;
        }

        for &(program_id, interface) in declarations {
            let substitutions = self.type_parameter_substitutions_for_reference(
                program_id,
                interface.type_parameters.as_deref(),
                reference,
            );
            if let Some(property) = interface.body.body.iter().find_map(|signature| {
                let TSSignature::TSPropertySignature(property) = signature else {
                    return None;
                };
                (property_key_name_str(&property.key) == Some(property_name)).then_some(property)
            }) {
                let ty = property
                    .type_annotation
                    .as_deref()
                    .map_or_else(Ty::any, |annotation| {
                        self.get_type_from_ts_type(program_id, &annotation.type_annotation)
                    });
                return Some(ty.substitute_type_parameters(self.arena(), &substitutions));
            }
        }

        let method_signatures = declarations
            .iter()
            .copied()
            .flat_map(|(program_id, interface)| {
                let substitutions = self.type_parameter_substitutions_for_reference(
                    program_id,
                    interface.type_parameters.as_deref(),
                    reference,
                );
                interface.body.body.iter().filter_map(move |signature| {
                    let TSSignature::TSMethodSignature(method) = signature else {
                        return None;
                    };
                    (property_key_name_str(&method.key) == Some(property_name)).then(|| {
                        self.signature_from_function_parts(
                            program_id,
                            SignatureKind::Call,
                            method.type_parameters.as_deref(),
                            method.params.as_ref(),
                            method.return_type.as_deref(),
                        )
                        .substitute_type_parameters(self.arena(), &substitutions)
                    })
                })
            })
            .collect::<Vec<_>>();
        match method_signatures.as_slice() {
            [] => None,
            [signature] => Some(Ty::Function(signature.function)),
            _ => Some(Ty::object_with_signatures(
                self.arena(),
                [],
                method_signatures,
            )),
        }
    }

    fn get_property_type_of_interface_declaration(
        &self,
        program_id: program::ProgramId,
        declaration: NodeId,
        reference: &TyTypeReference<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSInterfaceDeclaration(interface) => {
                let substitutions = self.type_parameter_substitutions_for_reference(
                    program_id,
                    interface.type_parameters.as_deref(),
                    reference,
                );
                if let Some(property) = interface.body.body.iter().find_map(|signature| {
                    let TSSignature::TSPropertySignature(property) = signature else {
                        return None;
                    };
                    (property_key_name_str(&property.key) == Some(property_name))
                        .then_some(property)
                }) {
                    let ty =
                        property
                            .type_annotation
                            .as_deref()
                            .map_or_else(Ty::any, |annotation| {
                                self.get_type_from_ts_type(program_id, &annotation.type_annotation)
                            });
                    return Some(ty.substitute_type_parameters(self.arena(), &substitutions));
                }

                let method_signatures = interface
                    .body
                    .body
                    .iter()
                    .filter_map(|signature| {
                        let TSSignature::TSMethodSignature(method) = signature else {
                            return None;
                        };
                        (property_key_name_str(&method.key) == Some(property_name)).then(|| {
                            self.signature_from_function_parts(
                                program_id,
                                SignatureKind::Call,
                                method.type_parameters.as_deref(),
                                method.params.as_ref(),
                                method.return_type.as_deref(),
                            )
                            .substitute_type_parameters(self.arena(), &substitutions)
                        })
                    })
                    .collect::<Vec<_>>();
                match method_signatures.as_slice() {
                    [] => None,
                    [signature] => Some(Ty::Function(signature.function)),
                    _ => {
                        // TODO(overloads): model overloaded methods as structured callable members
                        // with TypeScript Go's full signature-list metadata, not an empty object
                        // carrying call signatures only.
                        Some(Ty::object_with_signatures(
                            self.arena(),
                            [],
                            method_signatures,
                        ))
                    }
                }
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_property_type_of_interface_declaration(
                    program_id,
                    parent_id,
                    reference,
                    property_name,
                )
            }
            _ => None,
        }
    }

    fn get_type_of_ts_method_signature_location(
        &self,
        program_id: program::ProgramId,
        node_id: NodeId,
        method: &'a oxc_ast::ast::TSMethodSignature<'a>,
    ) -> Ty<'a> {
        let Some(method_name) = property_key_name_str(&method.key) else {
            let signature = self.signature_from_function_parts(
                program_id,
                SignatureKind::Call,
                method.type_parameters.as_deref(),
                method.params.as_ref(),
                method.return_type.as_deref(),
            );
            return Ty::Function(signature.function);
        };

        let Some(current_interface) =
            self.nodes(program_id)
                .ancestor_kinds(node_id)
                .find_map(|kind| match kind {
                    AstKind::TSInterfaceDeclaration(interface) => Some(interface),
                    _ => None,
                })
        else {
            let signature = self.signature_from_function_parts(
                program_id,
                SignatureKind::Call,
                method.type_parameters.as_deref(),
                method.params.as_ref(),
                method.return_type.as_deref(),
            );
            return Ty::Function(signature.function);
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
            .interface_declarations_for_name(current_interface.id.name.as_str())
            .iter()
            .copied()
            .flat_map(|(interface_program_id, interface)| {
                let substitutions = self.type_parameter_substitutions_for_type_arguments(
                    interface_program_id,
                    interface.type_parameters.as_deref(),
                    &current_type_arguments,
                );
                interface.body.body.iter().filter_map(move |signature| {
                    let TSSignature::TSMethodSignature(candidate) = signature else {
                        return None;
                    };
                    (property_key_name_str(&candidate.key) == Some(method_name)).then(|| {
                        self.signature_from_function_parts(
                            interface_program_id,
                            SignatureKind::Call,
                            candidate.type_parameters.as_deref(),
                            candidate.params.as_ref(),
                            candidate.return_type.as_deref(),
                        )
                        .substitute_type_parameters(self.arena(), &substitutions)
                    })
                })
            })
            .collect::<Vec<_>>();

        match method_signatures.as_slice() {
            [] => {
                let signature = self.signature_from_function_parts(
                    program_id,
                    SignatureKind::Call,
                    method.type_parameters.as_deref(),
                    method.params.as_ref(),
                    method.return_type.as_deref(),
                );
                Ty::Function(signature.function)
            }
            [signature] => Ty::Function(signature.function),
            _ => Ty::object_with_signatures(self.arena(), [], method_signatures),
        }
    }

    fn type_parameter_substitutions_for_reference(
        &self,
        program_id: program::ProgramId,
        type_parameters: Option<&'a oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        reference: &TyTypeReference<'a>,
    ) -> HashMap<&'a str, Ty<'a>> {
        self.type_parameter_substitutions_for_type_arguments(
            program_id,
            type_parameters,
            reference.type_arguments.as_slice(),
        )
    }

    fn type_parameter_substitutions_for_type_arguments(
        &self,
        program_id: program::ProgramId,
        type_parameters: Option<&'a oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        type_arguments: &[Ty<'a>],
    ) -> HashMap<&'a str, Ty<'a>> {
        let type_parameters = self.type_parameters_from_declaration(program_id, type_parameters);
        let mut substitutions = HashMap::new();

        for (type_parameter, type_argument) in type_parameters.iter().zip(type_arguments.iter()) {
            substitutions.insert(type_parameter.name, *type_argument);
        }

        for type_parameter in type_parameters.iter().skip(type_arguments.len()) {
            let Some(default_type) = type_parameter.default_type else {
                break;
            };
            let default_type = default_type.substitute_type_parameters(
                self.arena(),
                &self.substitutions_with_unresolved_type_parameters_as_any(
                    &type_parameters,
                    &substitutions,
                ),
            );
            substitutions.insert(type_parameter.name, default_type);
        }

        substitutions
    }

    fn substitutions_with_unresolved_type_parameters_as_any(
        &self,
        type_parameters: &[TyTypeParameter<'a>],
        substitutions: &HashMap<&'a str, Ty<'a>>,
    ) -> HashMap<&'a str, Ty<'a>> {
        let mut substitutions = substitutions.clone();
        for type_parameter in type_parameters {
            substitutions
                .entry(type_parameter.name)
                .or_insert_with(Ty::any);
        }
        substitutions
    }

    fn type_parameters_from_declaration(
        &self,
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
        parameter: &'a TSTypeParameter<'a>,
    ) -> TyTypeParameter<'a> {
        Ty::type_parameter(
            parameter.name.name.as_str(),
            parameter
                .constraint
                .as_ref()
                .map(|constraint| self.get_type_from_ts_type(program_id, constraint)),
            parameter.default.as_ref().map(|default| {
                self.get_apparent_type_at_use(
                    program_id,
                    self.get_type_from_ts_type(program_id, default),
                    0,
                )
            }),
        )
    }

    pub fn get_class_symbol_for_type(
        &self,
        program_id: program::ProgramId,
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

    pub fn get_root_symbol(&self, program_id: program::ProgramId, name: &str) -> Option<SymbolRef> {
        self.semantic(program_id)
            .scoping()
            .get_root_binding(Ident::from(name))
            .map(|symbol_id| SymbolRef::new(program_id, symbol_id))
    }

    fn interface_declarations_for_name(
        &self,
        type_name: &str,
    ) -> &'a [(program::ProgramId, &'a TSInterfaceDeclaration<'a>)] {
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
        program_id: program::ProgramId,
        type_name: &str,
    ) -> Option<Vec<TyTypeParameter<'a>>> {
        let symbol = self.get_type_symbol_for_name(program_id, type_name)?;
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.get_type_parameters_for_declaration(symbol.program_id, declaration)
    }

    fn get_type_parameters_for_declaration(
        &self,
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
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

    fn get_class_member_type(
        &self,
        program_id: program::ProgramId,
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
                return Some(Ty::any());
            }
            resolving_class_members.push(resolution);
        }

        let ty = class.body.body.iter().find_map(|element| match element {
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
        });

        self.resolving_class_members.borrow_mut().pop();
        ty
    }

    /// Resolve the type of a method definition on a class.
    /// Getters can turn into non-function types, but generally this returns a function type.
    fn get_type_of_method_definition(
        &self,
        program_id: program::ProgramId,
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
            && let Ty::Function(func) = inferred_method_type
        {
            return func.return_type;
        }

        inferred_method_type
    }

    /// Resolve a class field's declared or inferred type.
    /// Class member lookups and declaration records use this to agree on annotation-first behavior.
    fn get_type_of_property_definition(
        &self,
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
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
            .function;
        callback_function
            .parameters
            .get(parameter_index)
            .map(|parameter| self.get_apparent_type_at_use(program_id, parameter.ty, 0))
    }

    fn get_apparent_contextual_parameter_type(
        &self,
        program_id: program::ProgramId,
        ty: Ty<'a>,
    ) -> Ty<'a> {
        if let Ty::TypeReference(reference) = ty
            && self.is_conditional_type_alias_reference(program_id, reference)
            && let Some((expanded_program_id, expanded)) =
                self.get_conditional_type_alias_reference_type(program_id, reference)
        {
            if matches!(expanded, Ty::Conditional(_)) {
                let apparent =
                    self.apparent_type_for_conditional_match(expanded_program_id, expanded, 0);
                return if matches!(apparent, Ty::Conditional(_)) {
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
        program_id: program::ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> Option<(program::ProgramId, Ty<'a>)> {
        let symbol = self.get_type_symbol_for_name(program_id, reference.name)?;
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.get_conditional_type_alias_declaration_type(symbol.program_id, declaration, reference)
            .map(|ty| (symbol.program_id, ty))
    }

    fn get_conditional_type_alias_declaration_type(
        &self,
        program_id: program::ProgramId,
        declaration: NodeId,
        reference: &TyTypeReference<'a>,
    ) -> Option<Ty<'a>> {
        match self.nodes(program_id).kind(declaration) {
            AstKind::TSTypeAliasDeclaration(alias)
                if matches!(alias.type_annotation, TSType::TSConditionalType(_)) =>
            {
                let substitutions = self.type_parameter_substitutions_for_reference(
                    program_id,
                    alias.type_parameters.as_deref(),
                    reference,
                );
                Some(
                    self.get_type_from_ts_type(program_id, &alias.type_annotation)
                        .substitute_type_parameters(self.arena(), &substitutions),
                )
            }
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(program_id).parent_id(declaration);
                self.get_conditional_type_alias_declaration_type(program_id, parent_id, reference)
            }
            _ => None,
        }
    }

    fn get_apparent_type_at_use(
        &self,
        program_id: program::ProgramId,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match ty {
            Ty::TypeReference(_) => self.get_apparent_contextual_parameter_type(program_id, ty),
            Ty::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.get_apparent_type_at_use(program_id, *ty, depth + 1)),
            ),
            Ty::Function(function) => Ty::function_with_type_predicate(
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
            ),
            _ => ty,
        }
    }

    fn is_conditional_type_alias_reference(
        &self,
        program_id: program::ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> bool {
        let Some(symbol) = self.get_type_symbol_for_name(program_id, reference.name) else {
            return false;
        };
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.is_conditional_type_alias_declaration(symbol.program_id, declaration)
    }

    fn is_conditional_type_alias_declaration(
        &self,
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
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
                self.get_contextual_type_of_binding_initializer(program_id, node_id, function_span)
            })
            .or_else(|| {
                self.get_contextual_type_of_return_expression(program_id, node_id, function_span)
            })
    }

    fn get_contextual_type_of_call_argument(
        &self,
        program_id: program::ProgramId,
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
        let parameter_type =
            self.get_call_parameter_type_at(callee_signature.function, argument_index)?;
        Some(parameter_type.substitute_type_parameters(
            self.arena(),
            &self.explicit_call_type_parameter_substitutions(
                program_id,
                callee_signature.function,
                call_expression,
            ),
        ))
    }

    fn get_contextual_type_of_construct_argument(
        &self,
        program_id: program::ProgramId,
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
        let parameter_type =
            self.get_call_parameter_type_at(construct_signature.function, argument_index)?;
        Some(parameter_type.substitute_type_parameters(
            self.arena(),
            &self.explicit_construct_type_parameter_substitutions(
                program_id,
                construct_signature.function,
                new_expression,
            ),
        ))
    }

    fn get_contextual_type_of_object_property_value(
        &self,
        program_id: program::ProgramId,
        node_id: NodeId,
        value_span: Span,
    ) -> Option<Ty<'a>> {
        let mut property_name = None;
        let mut object_span = None;

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
                    object_span = Some(object.span);
                    break;
                }
                _ => {}
            }
        }

        let property_name = property_name?;
        let object_context =
            self.get_contextual_type_of_call_argument(program_id, node_id, object_span?)?;

        self.get_destructured_property_type(program_id, object_context, property_name)
    }

    fn get_contextual_type_of_binding_initializer(
        &self,
        program_id: program::ProgramId,
        node_id: NodeId,
        function_span: Span,
    ) -> Option<Ty<'a>> {
        self.nodes(program_id)
            .ancestors_enumerated(node_id)
            .find_map(|(ancestor_id, node)| match node.kind() {
                AstKind::FormalParameter(parameter) => {
                    binding_pattern_default_initializer_symbol_id(&parameter.pattern, function_span)
                        .and_then(|symbol_id| {
                            self.get_type_of_formal_parameter_binding(
                                program_id,
                                ancestor_id,
                                parameter,
                                symbol_id,
                            )
                        })
                }
                AstKind::VariableDeclarator(declarator) => {
                    binding_pattern_default_initializer_symbol_id(&declarator.id, function_span)
                        .and_then(|symbol_id| {
                            self.get_type_of_variable_declarator_binding(
                                program_id,
                                ancestor_id,
                                declarator,
                                symbol_id,
                            )
                        })
                }
                _ => None,
            })
    }

    fn get_contextual_type_of_return_expression(
        &self,
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
        function: FunctionKind<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let function_span = match function {
            FunctionKind::Function(f) => f.span,
            FunctionKind::ArrowFunction(f) => f.span,
        };
        let contextual_function = node_id
            .and_then(|node_id| {
                self.get_contextual_type_of_function_expression(program_id, node_id, function_span)
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
            .map(|signature| signature.function);
        let type_parameters = match function {
            FunctionKind::Function(f) => {
                self.type_parameters_from_declaration(program_id, f.type_parameters.as_deref())
            }
            FunctionKind::ArrowFunction(f) => {
                self.type_parameters_from_declaration(program_id, f.type_parameters.as_deref())
            }
        };
        let parameters = match function {
            FunctionKind::Function(f) => self.function_signature_parameters_with_context(
                program_id,
                &f.params,
                contextual_function,
            ),
            FunctionKind::ArrowFunction(f) => self.function_signature_parameters_with_context(
                program_id,
                &f.params,
                contextual_function,
            ),
        };
        let return_type = match function {
            FunctionKind::Function(f) => f.return_type.as_deref().map_or_else(
                || self.infer_function_return_type(program_id, function, node_id),
                |annotation| self.get_type_from_ts_type_annotation(program_id, Some(annotation)),
            ),
            FunctionKind::ArrowFunction(f) => f.return_type.as_deref().map_or_else(
                || self.infer_function_return_type(program_id, function, node_id),
                |annotation| self.get_type_from_ts_type_annotation(program_id, Some(annotation)),
            ),
        };

        let explicit_return_type = match function {
            FunctionKind::Function(f) => f.return_type.as_deref(),
            FunctionKind::ArrowFunction(f) => f.return_type.as_deref(),
        };
        let (return_type, type_predicate) = match explicit_return_type {
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
        program_id: program::ProgramId,
        params: &'a FormalParameters<'a>,
    ) -> Vec<TyParameter<'a>> {
        self.function_signature_parameters_with_context(program_id, params, None)
    }

    fn function_type_parameters(
        &self,
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
        type_annotation: Option<&'a TSTypeAnnotation<'a>>,
    ) -> Ty<'a> {
        let ty = self.get_type_from_ts_type_annotation(program_id, type_annotation);
        self.get_apparent_type_at_use(program_id, ty, 0)
    }

    pub(crate) fn get_async_function_return_type(
        &self,
        program_id: program::ProgramId,
        return_type: Ty<'a>,
    ) -> Ty<'a> {
        match self.get_global_promise_type(program_id) {
            Some(Ty::TypeReference(reference)) => {
                // TODO(correctness): TypeScript wraps async returns with Promise<Awaited<T>>.
                Ty::type_reference(self.arena(), reference.name, [return_type])
            }
            _ => Ty::any(),
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
        program_id: program::ProgramId,
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

    fn get_module_namespace_type(
        &self,
        program_id: program::ProgramId,
        namespace_name: &str,
    ) -> Ty<'a> {
        let Some(entry) = self.store.entry(program_id) else {
            return Ty::any();
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
                    ExportLocalName::Null => return None,
                };
                let symbol = self.get_root_symbol(program_id, local_name)?;
                Some(Ty::property(property_name, self.get_type_of_symbol(symbol)))
            });
        Ty::module_namespace(self.arena(), namespace_name, properties)
    }

    fn get_type_of_array_expression(
        &self,
        program_id: program::ProgramId,
        array_expression: &'a ArrayExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        match array_expression.elements.len() {
            0 => Ty::array(
                self.arena,
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
                let element_type =
                    self.get_type_of_array_expression_element(program_id, first_element, node_id);
                Ty::array(self.arena, element_type)
            }
            // For 2+ elements: try to create a union type if there are mixed types
            _ => {
                // TODO(perf): avoid allocating here somehow?
                let mut element_types = Vec::default();
                for element in &array_expression.elements {
                    let element_type =
                        self.get_type_of_array_expression_element(program_id, element, node_id);
                    // TODO(perf): avoid re-iterating elements? use a hash set?
                    if !element_types.contains(&element_type) {
                        element_types.push(element_type);
                    }
                }
                let element_type = if element_types.len() == 1 {
                    element_types[0]
                } else {
                    Ty::union(self.arena, element_types)
                };
                Ty::array(self.arena, element_type)
            }
        }
    }

    fn get_type_of_array_expression_element(
        &self,
        program_id: program::ProgramId,
        element: &'a ArrayExpressionElement<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        match element {
            ArrayExpressionElement::SpreadElement(spread) => {
                let argument_type = self.get_type_of_expression_with_node(
                    program_id,
                    &spread.argument,
                    node_id,
                    GetTypeFlags::NONE,
                );
                argument_type.array_element_type().unwrap_or_else(Ty::any)
            }
            ArrayExpressionElement::Elision(_) => Ty::any(),
            _ => self.get_type_of_expression_with_node(
                program_id,
                element.to_expression(),
                node_id,
                GetTypeFlags::NONE,
            ),
        }
    }

    fn get_type_of_function_declaration_group(
        &self,
        program_id: program::ProgramId,
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

        let function_declarations =
            self.function_declarations_for_value_symbol(program_id, symbol_id, function_name);

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
            return self.get_type_of_function_signature_with_node(
                program_id,
                FunctionKind::Function(function),
                Some(node_id),
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
                let Ty::Function(function) = self.get_type_of_function_signature_with_node(
                    declaration_program_id,
                    FunctionKind::Function(declaration),
                    Some(declaration_id),
                ) else {
                    unreachable!("function declarations resolve to function types")
                };
                Signature::new(SignatureKind::Call, function)
            },
        );
        Ty::object_with_signatures(self.arena(), [], signatures)
    }

    fn has_class_declaration_named(&self, program_id: program::ProgramId, name: &str) -> bool {
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
        program_id: program::ProgramId,
        symbol_id: SymbolId,
        function_name: &'a str,
    ) -> Vec<(program::ProgramId, NodeId, &'a Function<'a>)> {
        let scoping = self.semantic(program_id).scoping();
        let is_root_function =
            scoping.get_root_binding(Ident::from(function_name)) == Some(symbol_id);

        if !is_root_function || !self.is_global_script_entry(program_id) {
            return self.function_declarations_for_symbol(program_id, symbol_id);
        }

        let mut seen = HashSet::new();
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
            .filter(|(program_id, declaration_id, _)| seen.insert((*program_id, *declaration_id)))
            .collect()
    }

    fn function_declarations_for_symbol(
        &self,
        program_id: program::ProgramId,
        symbol_id: SymbolId,
    ) -> Vec<(program::ProgramId, NodeId, &'a Function<'a>)> {
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

    fn is_global_script_entry(&self, program_id: program::ProgramId) -> bool {
        self.store.entry(program_id).is_some_and(|entry| {
            entry.module_record().requested_modules.is_empty()
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
        program_id: program::ProgramId,
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

    fn get_type_of_variable_declarator(
        &self,
        program_id: program::ProgramId,
        declaration: NodeId,
        declarator: &'a VariableDeclarator<'a>,
    ) -> Ty<'a> {
        if declarator.type_annotation.is_some() {
            self.get_type_from_ts_type_annotation(program_id, declarator.type_annotation.as_deref())
        } else {
            declarator.init.as_ref().map_or_else(
                || {
                    self.get_type_of_for_of_declarator(program_id, declaration, declarator)
                        .unwrap_or_else(Ty::any)
                },
                |expression| {
                    let flags = if declarator.kind == VariableDeclarationKind::Const
                        && !self.is_in_exported_declaration(program_id, declaration)
                    {
                        GetTypeFlags::PRESERVE_LITERALS
                    } else {
                        GetTypeFlags::NONE
                    };
                    self.get_type_of_expression_with_node(
                        program_id,
                        expression,
                        Some(declaration),
                        flags,
                    )
                },
            )
        }
    }

    fn get_type_of_for_of_declarator(
        &self,
        program_id: program::ProgramId,
        declaration: NodeId,
        declarator: &'a VariableDeclarator<'a>,
    ) -> Option<Ty<'a>> {
        let (for_of_node_id, for_of) = self
            .nodes(program_id)
            .ancestors_enumerated(declaration)
            .find_map(|(ancestor_id, node)| match node.kind() {
                AstKind::ForOfStatement(for_of)
                    if for_statement_left_contains_declarator(&for_of.left, declarator) =>
                {
                    Some((ancestor_id, for_of))
                }
                _ => None,
            })?;

        let iterable_type = self.get_type_of_expression_with_node(
            program_id,
            &for_of.right,
            Some(for_of_node_id),
            GetTypeFlags::NONE,
        );
        self.get_iteration_element_type(program_id, for_of_node_id, iterable_type, for_of.r#await)
    }

    fn get_type_of_variable_declarator_binding(
        &self,
        program_id: program::ProgramId,
        declaration: NodeId,
        declarator: &'a VariableDeclarator<'a>,
        symbol_id: SymbolId,
    ) -> Option<Ty<'a>> {
        let binding_type =
            self.get_type_of_variable_declarator(program_id, declaration, declarator);
        self.get_type_of_binding_pattern_symbol(program_id, &declarator.id, symbol_id, binding_type)
    }

    fn get_type_of_formal_parameter_binding(
        &self,
        program_id: program::ProgramId,
        parameter_node_id: NodeId,
        parameter: &'a FormalParameter<'a>,
        symbol_id: SymbolId,
    ) -> Option<Ty<'a>> {
        let binding_type = parameter.type_annotation.as_deref().map_or_else(
            || {
                self.get_contextual_type_of_formal_parameter(
                    program_id,
                    parameter_node_id,
                    parameter,
                )
                .unwrap_or_else(Ty::any)
            },
            |annotation| {
                self.get_declared_type_of_formal_parameter(program_id, parameter, annotation)
            },
        );
        self.get_type_of_binding_pattern_symbol(
            program_id,
            &parameter.pattern,
            symbol_id,
            binding_type,
        )
    }

    fn get_type_of_rest_parameter_binding(
        &self,
        program_id: program::ProgramId,
        parameter: &'a FormalParameterRest<'a>,
        symbol_id: SymbolId,
    ) -> Option<Ty<'a>> {
        let binding_type = self.get_parameter_type_from_ts_type_annotation(
            program_id,
            parameter.type_annotation.as_deref(),
        );
        self.get_type_of_binding_pattern_symbol(
            program_id,
            &parameter.rest.argument,
            symbol_id,
            binding_type,
        )
    }

    fn get_type_of_binding_identifier_from_binding_pattern(
        &self,
        program_id: program::ProgramId,
        node_id: NodeId,
        symbol_id: SymbolId,
    ) -> Option<Ty<'a>> {
        self.nodes(program_id)
            .ancestors_enumerated(node_id)
            .find_map(|(ancestor_id, ancestor)| match ancestor.kind() {
                AstKind::FormalParameter(parameter) => self.get_type_of_formal_parameter_binding(
                    program_id,
                    ancestor_id,
                    parameter,
                    symbol_id,
                ),
                AstKind::FormalParameterRest(parameter) => {
                    self.get_type_of_rest_parameter_binding(program_id, parameter, symbol_id)
                }
                AstKind::VariableDeclarator(declarator) => self
                    .get_type_of_variable_declarator_binding(
                        program_id,
                        ancestor_id,
                        declarator,
                        symbol_id,
                    ),
                _ => None,
            })
    }

    fn get_type_of_binding_pattern_symbol(
        &self,
        program_id: program::ProgramId,
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
                    let element_type = tuple_element_type_at_index(&pattern_type, index)
                        .or_else(|| pattern_type.array_element_type())
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
                            .array_element_type()
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

    fn get_apparent_binding_type(&self, program_id: program::ProgramId, ty: Ty<'a>) -> Ty<'a> {
        self.get_apparent_type_at_use(program_id, ty, 0)
    }

    fn get_non_undefined_type(&self, ty: Ty<'a>) -> Ty<'a> {
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
            Ty::union(self.arena(), types)
        }
    }

    fn get_destructured_property_type(
        &self,
        program_id: program::ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        self.get_destructured_property_type_at_depth(program_id, object_type, property_name, 0)
    }

    fn get_destructured_property_type_at_depth(
        &self,
        program_id: program::ProgramId,
        object_type: Ty<'a>,
        property_name: &str,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return object_type.property_type(property_name);
        }

        match object_type {
            Ty::Object(object) => object.properties.iter().find_map(|property| {
                if property.computed || property.name != property_name {
                    return None;
                }
                Some(if property.optional {
                    Ty::union(self.arena(), [property.ty, Ty::undefined()])
                } else {
                    property.ty
                })
            }),
            Ty::ModuleNamespace(namespace) => namespace.properties.iter().find_map(|property| {
                (property.name == property_name && !property.computed).then_some(property.ty)
            }),
            Ty::Union(union) => {
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
            Ty::Intersection(intersection) => intersection.types.iter().find_map(|ty| {
                self.get_destructured_property_type_at_depth(
                    program_id,
                    *ty,
                    property_name,
                    depth + 1,
                )
            }),
            Ty::TypeReference(reference) => self
                .get_expanded_type_alias_reference_type(program_id, reference, depth + 1)
                .and_then(|(expanded_program_id, expanded)| {
                    self.get_destructured_property_type_at_depth(
                        expanded_program_id,
                        expanded,
                        property_name,
                        depth + 1,
                    )
                })
                .or_else(|| {
                    self.get_property_type_of_interface_type(program_id, reference, property_name)
                }),
            _ => None,
        }
    }

    fn get_expanded_type_alias_reference_type(
        &self,
        program_id: program::ProgramId,
        reference: &TyTypeReference<'a>,
        depth: usize,
    ) -> Option<(program::ProgramId, Ty<'a>)> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return None;
        }
        let symbol = self.get_type_symbol_for_name(program_id, reference.name)?;
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        self.get_expanded_type_alias_declaration(
            symbol.program_id,
            declaration,
            reference.type_arguments.as_slice(),
            depth + 1,
        )
        .map(|ty| (symbol.program_id, ty))
    }

    fn get_declared_type_of_formal_parameter(
        &self,
        program_id: program::ProgramId,
        parameter: &'a FormalParameter<'a>,
        annotation: &'a TSTypeAnnotation<'a>,
    ) -> Ty<'a> {
        let annotated_type =
            self.get_parameter_type_from_ts_type_annotation(program_id, Some(annotation));

        if parameter.optional {
            return Ty::union(self.arena(), [annotated_type, Ty::undefined()]);
        }

        annotated_type
    }

    fn get_type_of_binding_identifier_without_symbol(
        &self,
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
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
        program_id: program::ProgramId,
        await_expr: &'a AwaitExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let ty = self.get_type_of_expression_with_node(
            program_id,
            &await_expr.argument,
            node_id,
            GetTypeFlags::NONE,
        );
        self.get_awaited_type(program_id, ty)
    }

    fn get_awaited_type(&self, program_id: program::ProgramId, ty: Ty<'a>) -> Ty<'a> {
        match ty {
            Ty::Union(union) => Ty::union(
                self.arena(),
                union
                    .types
                    .iter()
                    .map(|ty| self.get_awaited_type(program_id, *ty)),
            ),
            Ty::TypeReference(reference) if is_promise_like_type_reference(reference.name) => {
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
        program_id: program::ProgramId,
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
            .filter_map(|signature| signature.function.parameters.first())
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

    fn get_then_property_type(&self, program_id: program::ProgramId, ty: Ty<'a>) -> Option<Ty<'a>> {
        match ty {
            Ty::TypeReference(_) | Ty::TypeQuery(_) => {
                self.get_property_type_of_named_type(program_id, &ty, "then")
            }
            _ => self.get_property_type_for_indexed_access(program_id, ty, "then"),
        }
    }

    fn get_fulfilled_value_types(
        &self,
        program_id: program::ProgramId,
        callback_type: Ty<'a>,
    ) -> Vec<Ty<'a>> {
        match callback_type {
            Ty::Union(union) => union
                .types
                .iter()
                .filter(|ty| !matches!(ty, Ty::Null | Ty::Undefined | Ty::Never))
                .flat_map(|ty| self.get_fulfilled_value_types(program_id, *ty))
                .collect(),
            _ => self
                .get_signatures_of_type_in_program(program_id, callback_type, SignatureKind::Call)
                .iter()
                .filter_map(|signature| signature.function.parameters.first())
                .map(|parameter| parameter.ty)
                .collect(),
        }
    }

    fn get_iteration_element_type(
        &self,
        program_id: program::ProgramId,
        node_id: NodeId,
        iterable_type: Ty<'a>,
        is_await: bool,
    ) -> Option<Ty<'a>> {
        match iterable_type {
            Ty::Any => Some(Ty::any()),
            Ty::Union(union) => {
                let element_types = union
                    .types
                    .iter()
                    .filter_map(|ty| {
                        self.get_iteration_element_type(program_id, node_id, *ty, is_await)
                    })
                    .collect::<Vec<_>>();
                (!element_types.is_empty()).then(|| Ty::union(self.arena(), element_types))
            }
            Ty::Array(array) => Some(self.get_for_of_element_type(
                program_id,
                node_id,
                array.element_type,
                is_await,
            )),
            Ty::Tuple(tuple) => Some(self.get_for_of_element_type(
                program_id,
                node_id,
                Ty::union(
                    self.arena(),
                    tuple.elements.iter().map(|element| element.ty()),
                ),
                is_await,
            )),
            Ty::TypeReference(reference) if is_iterable_type_reference(reference.name) => reference
                .type_arguments
                .first()
                .copied()
                .map(|element_type| {
                    self.get_for_of_element_type(program_id, node_id, element_type, is_await)
                }),
            _ => None,
        }
    }

    fn get_for_of_element_type(
        &self,
        program_id: program::ProgramId,
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

    pub(crate) fn is_scoped_type_parameter_reference(
        &self,
        program_id: program::ProgramId,
        node_id: NodeId,
        ty: Ty<'a>,
    ) -> bool {
        let Ty::TypeReference(reference) = ty else {
            return false;
        };
        if !reference.type_arguments.is_empty() {
            return false;
        }
        self.type_parameter_names_in_scope(program_id, node_id)
            .contains(&reference.name)
    }

    fn type_parameter_names_in_scope(
        &self,
        program_id: program::ProgramId,
        node_id: NodeId,
    ) -> Vec<&'a str> {
        let mut names = Vec::new();
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
}

impl<'a> Checker<'a> for CheckerReturn<'a, '_> {
    fn get_symbol_at_location(&self, node: NodeRef) -> Option<SymbolRef> {
        match self.node_kind(node) {
            AstKind::BindingIdentifier(identifier) => identifier
                .symbol_id
                .get()
                .map(|symbol_id| SymbolRef::new(node.program_id, symbol_id)),
            AstKind::IdentifierReference(identifier) => identifier
                .reference_id
                .get()
                .and_then(|reference_id| {
                    self.semantic(node.program_id)
                        .scoping()
                        .get_reference(reference_id)
                        .symbol_id()
                        .map(|symbol_id| SymbolRef::new(node.program_id, symbol_id))
                })
                .or_else(|| {
                    self.get_value_symbol_for_name(node.program_id, identifier.name.as_str())
                }),
            AstKind::TSTypeReference(reference) => match &reference.type_name {
                TSTypeName::IdentifierReference(identifier) => identifier
                    .reference_id
                    .get()
                    .and_then(|reference_id| {
                        self.semantic(node.program_id)
                            .scoping()
                            .get_reference(reference_id)
                            .symbol_id()
                            .map(|symbol_id| SymbolRef::new(node.program_id, symbol_id))
                    })
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
            AstKind::BindingIdentifier(identifier) => identifier.symbol_id.get().map_or_else(
                || {
                    self.get_type_of_binding_identifier_without_symbol(
                        node.program_id,
                        node.node_id,
                    )
                },
                |symbol_id| self.get_type_of_symbol(SymbolRef::new(node.program_id, symbol_id)),
            ),
            AstKind::IdentifierReference(identifier) => {
                self.get_symbol_at_location(node).map_or_else(
                    || {
                        if identifier.name == UNDEFINED_IDENT {
                            Ty::undefined()
                        } else {
                            self.get_value_symbol_for_name(
                                node.program_id,
                                identifier.name.as_str(),
                            )
                            .map_or_else(Ty::none, |symbol| self.get_type_of_symbol(symbol))
                        }
                    },
                    |symbol| {
                        let base_type = self.get_type_of_symbol(symbol);
                        flow::get_flow_type_of_reference(self, node, symbol, base_type)
                    },
                )
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
                let ty = if let Ty::Infer(infer) = ty {
                    Ty::type_reference(self.arena(), infer.type_parameter.name, [])
                } else {
                    ty
                };
                if property.optional {
                    Ty::union(self.arena(), [ty, Ty::undefined()])
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
                if self.is_in_contextually_typed_initializer(node.program_id, node.node_id)
                    && let Expression::BooleanLiteral(literal) = &property.value
                {
                    Ty::boolean_literal(literal.value)
                } else {
                    self.get_type_of_expression_with_node(
                        node.program_id,
                        &property.value,
                        Some(node.node_id),
                        GetTypeFlags::NONE,
                    )
                }
            }
            AstKind::StaticMemberExpression(member) => self.get_type_of_static_member_expression(
                node.program_id,
                member,
                Some(node.node_id),
            ),
            AstKind::ComputedMemberExpression(member) => self
                .get_type_of_computed_member_expression(
                    node.program_id,
                    member,
                    Some(node.node_id),
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
            AstKind::TSImportEqualsDeclaration(_) => Ty::any(),
            AstKind::TSInterfaceDeclaration(_) => Ty::any(),
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
            AstKind::TSInterfaceHeritage(_) => Ty::any(),
            AstKind::TSTypeReference(_) => {
                let ty = self
                    .get_symbol_at_location(node)
                    .map_or_else(Ty::any, |symbol| self.get_type_of_symbol(symbol));
                if ty.is_none() { Ty::any() } else { ty }
            }
            _ => self
                .get_symbol_at_location(node)
                .map_or_else(Ty::none, |sym| self.get_type_of_symbol(sym)),
        }
    }

    fn get_declared_type_of_symbol(&self, sym: SymbolRef) -> Ty<'a> {
        if let Some(ty) = self
            .declared_type_cache
            .borrow()
            .get(sym.program_id.index())
            .and_then(|cache| cache.get(sym.symbol_id))
            .copied()
            .flatten()
        {
            return ty;
        }

        let ty = if let Some((declaration, declarator)) = self.variable_declarator_for_symbol(sym) {
            return self.get_type_of_variable_declarator(sym.program_id, declaration, declarator);
        } else {
            let declaration = self
                .semantic(sym.program_id)
                .scoping()
                .symbol_declaration(sym.symbol_id);
            match self.nodes(sym.program_id).kind(declaration) {
                AstKind::VariableDeclarator(declarator) => self
                    .get_type_of_variable_declarator_binding(
                        sym.program_id,
                        declaration,
                        declarator,
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
                    .get_type_of_formal_parameter_binding(
                        sym.program_id,
                        declaration,
                        parameter,
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
                    .get_type_of_rest_parameter_binding(sym.program_id, parameter, sym.symbol_id)
                    .unwrap_or_else(|| {
                        self.get_type_from_ts_type_annotation(
                            sym.program_id,
                            parameter.type_annotation.as_deref(),
                        )
                    }),
                AstKind::CatchParameter(parameter) => self.get_type_from_ts_type_annotation(
                    sym.program_id,
                    parameter.type_annotation.as_deref(),
                ),
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

        if let Some(slot) = self
            .declared_type_cache
            .borrow_mut()
            .get_mut(sym.program_id.index())
            .and_then(|cache| cache.get_mut(sym.symbol_id))
        {
            *slot = Some(ty);
        }
        ty
    }

    fn get_type_of_symbol(&self, sym: SymbolRef) -> Ty<'a> {
        {
            let mut resolving_symbols = self.resolving_symbols.borrow_mut();
            if resolving_symbols.contains(&sym) {
                return Ty::any();
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
                    self.get_type_of_variable_declarator(sym.program_id, declaration, declarator)
                }
                _ => self.get_declared_type_of_symbol(sym),
            }
        };

        self.resolving_symbols.borrow_mut().pop();
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
        match t {
            Ty::Function(function) if kind == SignatureKind::Call => {
                vec![Signature::new(SignatureKind::Call, function)]
            }
            Ty::Object(object) => object
                .signatures
                .iter()
                .copied()
                .filter(|signature| signature.kind == kind)
                .collect(),
            Ty::Intersection(intersection) => {
                // TODO(overloads): TypeScript Go combines intersection signatures with
                // `CompositeSignature` metadata. Concatenation is conservative enough for
                // first-pass call resolution but loses combined type predicate/diagnostic data.
                intersection
                    .types
                    .iter()
                    .flat_map(|ty| self.get_signatures_of_type(*ty, kind))
                    .collect()
            }
            Ty::Union(union) => {
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

    // TODO(completeness): Implement this method
    fn get_index_infos_of_type(&self, _t: Ty<'a>) -> Vec<IndexInfo<'a>> {
        Vec::new()
    }

    fn is_assignable_to(&self, source: Ty<'a>, target: Ty<'a>) -> bool {
        relations::is_assignable_to(source, target)
    }

    fn type_to_string(&self, t: Ty<'a>, _location: NodeRef) -> String {
        t.to_type_string()
    }

    fn symbol_to_string(&self, s: SymbolRef, _location: NodeRef) -> String {
        self.semantic(s.program_id)
            .scoping()
            .symbol_name(s.symbol_id)
            .to_string()
    }
}
