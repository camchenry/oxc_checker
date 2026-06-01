#![allow(dead_code, unused_imports)]
use oxc_allocator::Allocator;
use oxc_ast::{
    AstKind,
    ast::{
        ArrayExpression, ArrayExpressionElement, ArrowFunctionExpression, AssignmentExpression,
        AwaitExpression, BinaryExpression, BindingPattern, BooleanLiteral, CallExpression, Class,
        ClassElement, ComputedMemberExpression, ConditionalExpression, Expression, ForOfStatement,
        ForStatementLeft, FormalParameter, FormalParameterRest, FormalParameters, Function,
        FunctionBody, IdentifierReference, MethodDefinition, MethodDefinitionKind, NewExpression,
        NumericLiteral, ObjectExpression, ObjectPropertyKind, Program, PropertyDefinition,
        PropertyKey, ReturnStatement, StaticMemberExpression, StringLiteral,
        TSInterfaceDeclaration, TSLiteral, TSMappedType, TSModuleDeclarationName, TSSignature,
        TSThisParameter, TSTupleElement, TSType, TSTypeAnnotation, TSTypeName,
        TSTypeOperatorOperator, TSTypeParameter, TSTypeQuery, TSTypeQueryExprName, TSTypeReference,
        UnaryExpression, VariableDeclarationKind, VariableDeclarator,
    },
};
use oxc_ast_visit::Visit;
use oxc_index::{IndexVec, nonmax::NonMaxU32};
use oxc_semantic::{AstNode, AstNodes, NodeId, Semantic, SemanticBuilder, SymbolId};
use oxc_span::{GetSpan, Span};
use oxc_str::{Ident, static_ident};
use oxc_syntax::{
    module_record::{ExportExportName, ExportLocalName},
    operator::{AssignmentOperator, BinaryOperator, UnaryOperator},
    scope::ScopeFlags,
};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

mod evolving_arrays;
mod flow;
mod global_lib;
mod global_types;
pub mod program;
mod relations;
mod types;

use types::*;

const UNDEFINED_IDENT: Ident = static_ident!("undefined");
const TYPE_EXPANSION_MAX_DEPTH: usize = 32;

#[derive(Debug, Clone, Copy)]
enum FunctionKind<'a> {
    Function(&'a Function<'a>),
    ArrowFunction(&'a ArrowFunctionExpression<'a>),
}

impl<'a> FunctionKind<'a> {
    fn returns_promise(self) -> bool {
        match self {
            FunctionKind::Function(function) => function.r#async && !function.generator,
            FunctionKind::ArrowFunction(function) => function.r#async,
        }
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

fn infer_type_parameter_from_types<'a>(
    parameter_type: &Ty<'a>,
    argument_type: &Ty<'a>,
    type_parameters: &[&'a str],
    substitutions: &mut HashMap<&'a str, Ty<'a>>,
) {
    match (parameter_type, argument_type) {
        (Ty::Union(parameter_union), _) => {
            infer_type_parameter_from_union(
                parameter_union.types.iter().copied(),
                argument_type,
                type_parameters,
                substitutions,
            );
        }
        (Ty::TypeReference(reference), _)
            if reference.type_arguments.is_empty() && type_parameters.contains(&reference.name) =>
        {
            match substitutions.get(reference.name) {
                Some(existing) if existing != argument_type => {
                    substitutions.insert(reference.name, Ty::any());
                }
                Some(_) => {}
                None => {
                    substitutions.insert(reference.name, *argument_type);
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
                infer_type_parameter_from_types(
                    parameter_type,
                    argument_type,
                    type_parameters,
                    substitutions,
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
                    infer_type_parameter_from_types(
                        &parameter_property.ty,
                        &argument_property.ty,
                        type_parameters,
                        substitutions,
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
                infer_type_parameter_from_types(
                    &parameter.ty,
                    &argument.ty,
                    type_parameters,
                    substitutions,
                );
            }
            infer_type_parameter_from_types(
                &parameter_function.return_type,
                &argument_function.return_type,
                type_parameters,
                substitutions,
            );
        }
        _ => {}
    }
}

fn infer_type_parameter_from_union<'a>(
    parameter_types: impl IntoIterator<Item = Ty<'a>>,
    argument_type: &Ty<'a>,
    type_parameters: &[&'a str],
    substitutions: &mut HashMap<&'a str, Ty<'a>>,
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
                matches!(ty, Ty::TypeReference(reference) if reference.type_arguments.is_empty() && type_parameters.contains(&reference.name))
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
        infer_type_parameter_from_types(&candidate, argument_type, type_parameters, substitutions);
    }
}

fn property_key_name(key: &PropertyKey<'_>) -> Option<String> {
    property_key_name_str(key).map(str::to_string)
}

fn property_key_name_str<'a>(key: &PropertyKey<'a>) -> Option<&'a str> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.name.as_str()),
        PropertyKey::Identifier(identifier) => Some(identifier.name.as_str()),
        PropertyKey::NumericLiteral(literal) => literal.raw.as_ref().map(|raw| raw.as_str()),
        PropertyKey::StringLiteral(literal) => Some(literal.value.as_str()),
        _ => None,
    }
}

fn property_key_span(key: &PropertyKey<'_>) -> Option<Span> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.span),
        _ => None,
    }
}

fn index_type_to_property_name<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> Option<&'a str> {
    match ty {
        Ty::StringLiteral(literal) => Some(literal.value),
        Ty::NumberLiteral(literal) => Some(literal.value),
        Ty::BooleanLiteral(value) => Some(if value { "true" } else { "false" }),
        Ty::TemplateLiteral(template) if template.expressions.is_empty() => {
            Some(template.quasis[0].value)
        }
        Ty::TypeReference(reference) if reference.type_arguments.is_empty() => Some(reference.name),
        Ty::String => Some(arena.str("string")),
        Ty::Number => Some(arena.str("number")),
        _ => None,
    }
}

fn ts_type_name_to_string(name: &TSTypeName<'_>) -> String {
    match name {
        TSTypeName::IdentifierReference(identifier) => identifier.name.to_string(),
        TSTypeName::QualifiedName(qualified) => {
            format!(
                "{}.{}",
                ts_type_name_to_string(&qualified.left),
                qualified.right.name
            )
        }
        TSTypeName::ThisExpression(_) => "this".to_string(),
    }
}

fn ts_type_name_to_str<'a>(arena: CheckerArena<'a>, name: &TSTypeName<'a>) -> &'a str {
    match name {
        TSTypeName::IdentifierReference(identifier) => identifier.name.as_str(),
        TSTypeName::QualifiedName(qualified) => {
            let left = ts_type_name_to_str(arena, &qualified.left);
            arena.str(&format!("{}.{}", left, qualified.right.name))
        }
        TSTypeName::ThisExpression(_) => "this",
    }
}

fn ts_type_contains_infer(ty: &TSType<'_>) -> bool {
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

fn is_mapped_empty_object_intersection(ty: &TSType<'_>) -> bool {
    let TSType::TSIntersectionType(intersection) = ty else {
        return false;
    };

    let mut has_mapped = false;
    let mut has_empty_object = false;
    for ty in &intersection.types {
        match ty {
            TSType::TSMappedType(_) => has_mapped = true,
            TSType::TSTypeLiteral(type_literal) if type_literal.members.is_empty() => {
                has_empty_object = true;
            }
            _ => return false,
        }
    }

    has_mapped && has_empty_object
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

/// Convert a `typeof` query target into a lookup key when it can be resolved locally.
fn ts_type_query_expr_name_to_str<'a>(
    arena: CheckerArena<'a>,
    name: &TSTypeQueryExprName<'a>,
) -> Option<&'a str> {
    match name {
        TSTypeQueryExprName::IdentifierReference(identifier) => Some(identifier.name.as_str()),
        TSTypeQueryExprName::QualifiedName(qualified) => {
            let left = ts_type_name_to_str(arena, &qualified.left);
            Some(arena.str(&format!("{}.{}", left, qualified.right.name)))
        }
        TSTypeQueryExprName::ThisExpression(_) => Some("this"),
        TSTypeQueryExprName::TSImportType(_) => None,
    }
}

fn binding_pattern_name(pattern: &BindingPattern<'_>) -> Option<String> {
    match pattern {
        BindingPattern::BindingIdentifier(identifier) => Some(identifier.name.to_string()),
        _ => None,
    }
}

fn binding_pattern_name_str<'a>(pattern: &BindingPattern<'a>) -> Option<&'a str> {
    match pattern {
        BindingPattern::BindingIdentifier(identifier) => Some(identifier.name.as_str()),
        _ => None,
    }
}

fn binding_pattern_symbol_id(pattern: &BindingPattern<'_>) -> Option<SymbolId> {
    match pattern {
        BindingPattern::BindingIdentifier(identifier) => identifier.symbol_id.get(),
        _ => None,
    }
}

fn binding_pattern_default_initializer_symbol_id(
    pattern: &BindingPattern<'_>,
    initializer_span: Span,
) -> Option<SymbolId> {
    match pattern {
        BindingPattern::BindingIdentifier(_) => None,
        BindingPattern::ObjectPattern(object) => object
            .properties
            .iter()
            .find_map(|property| {
                binding_pattern_default_initializer_symbol_id(&property.value, initializer_span)
            })
            .or_else(|| {
                object.rest.as_ref().and_then(|rest| {
                    binding_pattern_default_initializer_symbol_id(&rest.argument, initializer_span)
                })
            }),
        BindingPattern::ArrayPattern(array) => array
            .elements
            .iter()
            .flatten()
            .find_map(|element| {
                binding_pattern_default_initializer_symbol_id(element, initializer_span)
            })
            .or_else(|| {
                array.rest.as_ref().and_then(|rest| {
                    binding_pattern_default_initializer_symbol_id(&rest.argument, initializer_span)
                })
            }),
        BindingPattern::AssignmentPattern(assignment) => {
            if assignment.right.span() == initializer_span {
                binding_pattern_symbol_id(&assignment.left)
            } else {
                binding_pattern_default_initializer_symbol_id(&assignment.left, initializer_span)
            }
        }
    }
}

fn for_statement_left_contains_declarator(
    left: &ForStatementLeft<'_>,
    target: &VariableDeclarator<'_>,
) -> bool {
    match left {
        ForStatementLeft::VariableDeclaration(declaration) => declaration
            .declarations
            .iter()
            .any(|declarator| declarator.span == target.span),
        _ => false,
    }
}

/*

type Signature struct {
    flags                    SignatureFlags
    minArgumentCount         int32
    resolvedMinArgumentCount int32
    declaration              *ast.Node
    typeParameters           []*Type
    parameters               []*ast.Symbol
    thisParameter            *ast.Symbol
    resolvedReturnType       *Type
    resolvedTypePredicate    *TypePredicate
    target                   *Signature
    mapper                   *TypeMapper
    isolatedSignatureType    *Type
    composite                *CompositeSignature
}

type Checker interface {
    CheckFile(ctx context.Context, file *SourceFile) []Diagnostic
    GetGlobalDiagnostics() []Diagnostic

    GetSymbolAtLocation(node *Node) *Symbol
    GetTypeAtLocation(node *Node) *Type
    GetTypeFromTypeNode(node *Node) *Type

    GetDeclaredTypeOfSymbol(symbol *Symbol) *Type
    GetTypeOfSymbol(symbol *Symbol) *Type
    GetTypeOfSymbolAtLocation(symbol *Symbol, location *Node) *Type

    GetPropertiesOfType(t *Type) []*Symbol
    GetPropertyOfType(t *Type, name string) *Symbol
    GetSignaturesOfType(t *Type, kind SignatureKind) []*Signature
    GetIndexInfosOfType(t *Type) []*IndexInfo

    IsAssignableTo(source, target *Type) bool
    TypeToString(t *Type, location *Node) string
    SymbolToString(s *Symbol, location *Node) string
}

*/

trait Checker<'a> {
    fn get_symbol_at_location(&self, node: NodeRef) -> Option<SymbolRef>;
    fn get_type_at_location(&self, node: NodeRef) -> Ty<'a>;
    // fn get_type_from_type_node(&self, type_node: NodeRef) -> Ty<'a>;
    fn get_declared_type_of_symbol(&self, sym: SymbolRef) -> Ty<'a>;
    fn get_type_of_symbol(&self, sym: SymbolRef) -> Ty<'a>;
    fn get_type_of_symbol_at_location(&self, node: NodeRef) -> Ty<'a>;
    fn get_properties_of_type(&self, t: Ty<'a>) -> Vec<SymbolRef>;
    fn get_property_of_type(&self, t: Ty<'a>, name: &str) -> Option<SymbolRef>;
    fn get_signatures_of_type(&self, t: Ty<'a>, kind: SignatureKind) -> Vec<Signature<'a>>;
    fn get_index_infos_of_type(&self, t: Ty<'a>) -> Vec<IndexInfo<'a>>;
    fn is_assignable_to(&self, source: Ty<'a>, target: Ty<'a>) -> bool;
    fn type_to_string(&self, t: Ty<'a>, location: NodeRef) -> String;
    fn symbol_to_string(&self, s: SymbolRef, location: NodeRef) -> String;
}

struct CheckerBuilder {}

impl CheckerBuilder {
    fn new() -> Self {
        Self {}
    }

    fn build<'a, 'store>(
        &self,
        store: &'store program::ProgramStore<'a>,
    ) -> CheckerReturn<'a, 'store> {
        CheckerReturn {
            store,
            arena: CheckerArena::new(store.allocator()),
            global_symbols: global_types::GlobalSymbolTable::new(store),
            declared_type_cache: RefCell::new(
                store
                    .entries()
                    .iter()
                    .map(|entry| {
                        IndexVec::from_vec(vec![None; entry.semantic().scoping().symbols_len()])
                    })
                    .collect(),
            ),
            interface_declarations_cache: RefCell::new(HashMap::new()),
            resolving_symbols: RefCell::new(Vec::new()),
            resolving_class_members: RefCell::new(Vec::new()),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NodeRef {
    program_id: program::ProgramId,
    node_id: NodeId,
}

impl NodeRef {
    fn new(program_id: program::ProgramId, node_id: NodeId) -> Self {
        Self {
            program_id,
            node_id,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct SymbolRef {
    program_id: program::ProgramId,
    symbol_id: SymbolId,
}

impl SymbolRef {
    fn new(program_id: program::ProgramId, symbol_id: SymbolId) -> Self {
        Self {
            program_id,
            symbol_id,
        }
    }
}

struct CheckerReturn<'a, 'store> {
    store: &'store program::ProgramStore<'a>,
    arena: CheckerArena<'a>,
    global_symbols: global_types::GlobalSymbolTable,
    declared_type_cache: RefCell<Vec<IndexVec<SymbolId, Option<Ty<'a>>>>>,
    interface_declarations_cache:
        RefCell<HashMap<String, &'a [(program::ProgramId, &'a TSInterfaceDeclaration<'a>)]>>,
    resolving_symbols: RefCell<Vec<SymbolRef>>,
    resolving_class_members: RefCell<Vec<ClassMemberResolution>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClassMemberResolution {
    program_id: program::ProgramId,
    class_name: String,
    property_name: String,
    is_static: bool,
}

impl<'a, 'store> CheckerReturn<'a, 'store> {
    #[inline]
    fn entry(&self, program_id: program::ProgramId) -> &program::ProgramEntry<'a> {
        self.store
            .entry(program_id)
            .expect("store-backed checker must reference a valid program")
    }

    #[inline]
    fn semantic(&self, program_id: program::ProgramId) -> &Semantic<'a> {
        self.entry(program_id).semantic()
    }

    #[inline]
    fn nodes(&self, program_id: program::ProgramId) -> &AstNodes<'a> {
        self.semantic(program_id).nodes()
    }

    #[inline]
    fn node_kind(&self, node: NodeRef) -> AstKind<'a> {
        self.nodes(node.program_id).kind(node.node_id)
    }

    #[inline]
    fn arena(&self) -> CheckerArena<'a> {
        self.arena
    }

    fn get_type_of_expression(
        &self,
        program_id: program::ProgramId,
        expression: &'a Expression<'a>,
    ) -> Ty<'a> {
        self.get_type_of_expression_with_node(program_id, expression, None)
    }

    fn get_type_of_expression_at_node(
        &self,
        program_id: program::ProgramId,
        expression: &'a Expression<'a>,
        node_id: NodeId,
    ) -> Ty<'a> {
        self.get_type_of_expression_with_node(program_id, expression, Some(node_id))
    }

    /// Resolve an expression type with a semantic context node when ancestor context is needed.
    /// This keeps `this` and member expressions tied to the class or call site they appear in.
    fn get_type_of_expression_with_node(
        &self,
        program_id: program::ProgramId,
        expression: &'a Expression<'a>,
        node_id: Option<NodeId>,
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
            Expression::UnaryExpression(unary_expression) => {
                self.get_type_of_unary_expression(program_id, unary_expression, node_id)
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
                .get_type_of_expression_with_node(program_id, &parenthesized.expression, node_id),
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
            _ => Ty::from_expression(expression),
        }
    }

    fn get_type_of_const_initializer(
        &self,
        program_id: program::ProgramId,
        expression: &'a Expression<'a>,
        node_id: NodeId,
    ) -> Ty<'a> {
        match expression {
            Expression::NumericLiteral(literal) => self.get_type_of_numeric_literal(literal),
            Expression::StringLiteral(literal) => self.get_type_of_string_literal(literal),
            Expression::BooleanLiteral(literal) => self.get_type_of_boolean_literal(literal),
            Expression::UnaryExpression(unary_expression)
                if unary_expression.operator == UnaryOperator::UnaryNegation =>
            {
                match &unary_expression.argument {
                    Expression::NumericLiteral(literal) => {
                        let name = self
                            .arena()
                            .str(&format!("-{}", self.numeric_literal_name(literal)));
                        Ty::number_literal(self.arena(), name)
                    }
                    _ => self.get_type_of_unary_expression(
                        program_id,
                        unary_expression,
                        Some(node_id),
                    ),
                }
            }
            _ => self.get_type_of_expression_at_node(program_id, expression, node_id),
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

    fn get_type_of_numeric_literal(&self, literal: &NumericLiteral<'a>) -> Ty<'a> {
        let name = self.numeric_literal_name(literal);
        Ty::number_literal(self.arena(), name)
    }

    fn numeric_literal_name(&self, literal: &NumericLiteral<'a>) -> &'a str {
        literal.raw.as_ref().map_or_else(
            || self.arena().str(&literal.value.to_string()),
            |raw| raw.as_str(),
        )
    }

    fn get_type_of_string_literal(&self, literal: &StringLiteral<'a>) -> Ty<'a> {
        let name = literal.raw.as_ref().map_or_else(
            || self.arena().str(&format!("{:?}", literal.value.as_str())),
            |raw| raw.as_str(),
        );
        Ty::string_literal(self.arena(), name)
    }

    fn get_type_of_boolean_literal(&self, literal: &BooleanLiteral) -> Ty<'a> {
        Ty::boolean_literal(literal.value)
    }

    fn get_type_of_binary_expression(
        &self,
        program_id: program::ProgramId,
        binary_expression: &'a BinaryExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let left =
            self.get_type_of_expression_with_node(program_id, &binary_expression.left, node_id);
        let right =
            self.get_type_of_expression_with_node(program_id, &binary_expression.right, node_id);

        match binary_expression.operator {
            BinaryOperator::Addition
                if self.is_string_like_for_addition(left)
                    || self.is_string_like_for_addition(right) =>
            {
                Ty::string()
            }
            BinaryOperator::Addition
                if self.is_number_like_for_arithmetic(left)
                    && self.is_number_like_for_arithmetic(right) =>
            {
                Ty::number()
            }
            BinaryOperator::Subtraction
            | BinaryOperator::Multiplication
            | BinaryOperator::Division
            | BinaryOperator::Remainder
            | BinaryOperator::Exponential
                if self.is_number_like_for_arithmetic(left)
                    && self.is_number_like_for_arithmetic(right) =>
            {
                Ty::number()
            }
            _ => Ty::any(),
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
        );
        match assignment_expression.operator {
            AssignmentOperator::Assign => right,
            AssignmentOperator::Addition if self.is_string_like_for_addition(right) => Ty::string(),
            AssignmentOperator::Addition
            | AssignmentOperator::Subtraction
            | AssignmentOperator::Multiplication
            | AssignmentOperator::Division
            | AssignmentOperator::Remainder
            | AssignmentOperator::Exponential
                if self.is_number_like_for_arithmetic(right) =>
            {
                Ty::number()
            }
            _ => Ty::any(),
        }
    }

    fn get_type_of_conditional_expression(
        &self,
        program_id: program::ProgramId,
        conditional: &'a ConditionalExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let consequent =
            self.get_type_of_expression_with_node(program_id, &conditional.consequent, node_id);
        let alternate =
            self.get_type_of_expression_with_node(program_id, &conditional.alternate, node_id);

        Ty::union(self.arena(), [consequent, alternate])
    }

    fn get_type_of_unary_expression(
        &self,
        program_id: program::ProgramId,
        unary_expression: &'a UnaryExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let argument =
            self.get_type_of_expression_with_node(program_id, &unary_expression.argument, node_id);
        match unary_expression.operator {
            UnaryOperator::UnaryPlus | UnaryOperator::UnaryNegation | UnaryOperator::BitwiseNot
                if self.is_number_like_for_arithmetic(argument) =>
            {
                Ty::number()
            }
            UnaryOperator::LogicalNot => Ty::boolean(),
            UnaryOperator::Typeof => Ty::string(),
            UnaryOperator::Void => Ty::undefined(),
            _ => Ty::any(),
        }
    }

    fn is_number_like_for_arithmetic(&self, ty: Ty<'a>) -> bool {
        matches!(ty, Ty::Number | Ty::NumberLiteral(_))
    }

    fn is_string_like_for_addition(&self, ty: Ty<'a>) -> bool {
        matches!(ty, Ty::String | Ty::StringLiteral(_))
    }

    /// Resolve a TypeScript type annotation, if any.
    fn get_type_from_ts_type_annotation(
        &self,
        program_id: program::ProgramId,
        type_annotation: Option<&TSTypeAnnotation<'a>>,
    ) -> Ty<'a> {
        type_annotation.map_or_else(Ty::any, |type_annotation| {
            self.get_type_from_ts_type(program_id, &type_annotation.type_annotation)
        })
    }

    fn get_type_from_property_signature_annotation(
        &self,
        program_id: program::ProgramId,
        type_annotation: &TSTypeAnnotation<'a>,
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
    fn get_type_from_ts_type(&self, program_id: program::ProgramId, ty: &TSType<'a>) -> Ty<'a> {
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
            TSType::TSTemplateLiteralType(template_literal) => Ty::ts_template_literal(
                self.arena(),
                template_literal,
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
                    Ty::template_literal(self.arena(), template_literal.as_ref())
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
        mapped: &TSMappedType<'a>,
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
        query: &TSTypeQuery<'a>,
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

    fn get_type_of_type_alias_declaration(
        &self,
        program_id: program::ProgramId,
        alias: &oxc_ast::ast::TSTypeAliasDeclaration<'a>,
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
        ty: &TSType<'a>,
    ) -> Ty<'a> {
        self.get_type_from_ts_type_expanding_top_level_aliases_at_depth(program_id, ty, 0)
    }

    fn get_type_from_ts_type_expanding_top_level_aliases_at_depth(
        &self,
        program_id: program::ProgramId,
        ty: &TSType<'a>,
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
                .filter(|expanded| is_index_signature_object(*expanded))
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
            && is_number_index_type(index_type)
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
                if matches!(name_type, Ty::Never) {
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
        reference: &TSTypeReference<'a>,
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
        reference: &TSTypeReference<'a>,
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
        reference: &TSTypeReference<'a>,
    ) -> Ty<'a> {
        self.get_type_from_ts_type_reference_with_default_display(program_id, reference, false)
    }

    fn get_type_from_type_assertion(
        &self,
        program_id: program::ProgramId,
        ty: &TSType<'a>,
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
        reference: &TSTypeReference<'a>,
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
        reference: &TSTypeReference<'a>,
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
        ty: &TSType<'a>,
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
                let ty =
                    self.get_type_of_expression_with_node(program_id, &property.value, node_id);
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
        let object_type =
            self.get_type_of_expression_with_node(program_id, &member.object, node_id);
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
        let object_type =
            self.get_type_of_expression_with_node(program_id, &member.object, node_id);
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
        let Ty::TypeReference(reference) = interface_type else {
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
        let callee_type =
            self.get_type_of_expression_with_node(program_id, &call_expression.callee, node_id);
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
        signature: &TSSignature<'a>,
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
        signature: &TSSignature<'a>,
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
        type_parameters: Option<&oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        parameters: &FormalParameters<'a>,
        return_type: Option<&TSTypeAnnotation<'a>>,
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
        type_parameters: Option<&oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
        this_param: Option<&TSThisParameter<'a>>,
        parameters: &FormalParameters<'a>,
        return_type: Option<&TSTypeAnnotation<'a>>,
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
        return_type: Option<&TSTypeAnnotation<'a>>,
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

    fn infer_call_type_parameter_substitutions(
        &self,
        program_id: program::ProgramId,
        function: &TyFunction<'a>,
        call_expression: &'a CallExpression<'a>,
        node_id: Option<NodeId>,
    ) -> HashMap<&'a str, Ty<'a>> {
        let (mut substitutions, explicit_type_parameters) = self
            .explicit_type_parameter_substitutions(
                program_id,
                function,
                call_expression.type_arguments.as_deref(),
            );

        let inferable_type_parameters = function
            .type_parameters
            .iter()
            .map(|type_parameter| type_parameter.name)
            .filter(|type_parameter| !explicit_type_parameters.contains(type_parameter))
            .collect::<Vec<_>>();

        for (argument, parameter) in call_expression
            .arguments
            .iter()
            .zip(function.parameters.iter())
        {
            let Some(argument) = argument.as_expression() else {
                continue;
            };
            let argument_type =
                self.get_type_of_expression_with_node(program_id, argument, node_id);
            infer_type_parameter_from_types(
                &parameter.ty,
                &argument_type,
                &inferable_type_parameters,
                &mut substitutions,
            );
        }

        self.add_type_parameter_fallback_substitutions(function, &mut substitutions, false);

        substitutions
    }

    fn explicit_call_type_parameter_substitutions(
        &self,
        program_id: program::ProgramId,
        function: &TyFunction<'a>,
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

    fn explicit_type_parameter_substitutions(
        &self,
        program_id: program::ProgramId,
        function: &TyFunction<'a>,
        type_arguments: Option<&oxc_ast::ast::TSTypeParameterInstantiation<'a>>,
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

    fn add_type_parameter_fallback_substitutions(
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
            Some(array_element_type(parameter.ty).unwrap_or(parameter.ty))
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

    fn infer_construct_type_parameter_substitutions(
        &self,
        program_id: program::ProgramId,
        function: &TyFunction<'a>,
        new_expression: &'a NewExpression<'a>,
    ) -> HashMap<&'a str, Ty<'a>> {
        let (mut substitutions, explicit_type_parameters) = self
            .explicit_type_parameter_substitutions(
                program_id,
                function,
                new_expression.type_arguments.as_deref(),
            );

        let inferable_type_parameters = function
            .type_parameters
            .iter()
            .map(|type_parameter| type_parameter.name)
            .filter(|type_parameter| !explicit_type_parameters.contains(type_parameter))
            .collect::<Vec<_>>();

        for (argument, parameter) in new_expression
            .arguments
            .iter()
            .zip(function.parameters.iter())
        {
            let Some(argument) = argument.as_expression() else {
                continue;
            };
            let argument_type = self.get_type_of_expression(program_id, argument);
            infer_type_parameter_from_types(
                &parameter.ty,
                &argument_type,
                &inferable_type_parameters,
                &mut substitutions,
            );
        }

        self.add_type_parameter_fallback_substitutions(function, &mut substitutions, true);

        substitutions
    }

    fn explicit_construct_type_parameter_substitutions(
        &self,
        program_id: program::ProgramId,
        function: &TyFunction<'a>,
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
            let argument_type =
                self.get_type_of_expression_with_node(program_id, argument, node_id);
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
        type_parameters: Option<&oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
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
        type_parameters: Option<&oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
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
        declaration: Option<&oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
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
        parameter: &TSTypeParameter<'a>,
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

    fn get_class_symbol_for_type(
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

    fn get_root_symbol(&self, program_id: program::ProgramId, name: &str) -> Option<SymbolRef> {
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
                if property_key_name(&method.key).as_deref() == Some(property_name) =>
            {
                Some(self.get_type_of_method_definition(program_id, method, class_node_id))
            }
            ClassElement::PropertyDefinition(property)
                if property.r#static == is_static
                    && property_key_name(&property.key).as_deref() == Some(property_name) =>
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
                    self.get_type_of_expression_with_node(program_id, value, node_id)
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

    fn get_type_of_function_signature(
        &self,
        program_id: program::ProgramId,
        function: &'a Function<'a>,
    ) -> Ty<'a> {
        self.get_type_of_function_signature_with_node(
            program_id,
            FunctionKind::Function(function),
            None,
        )
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
        params: &FormalParameters<'a>,
    ) -> Vec<TyParameter<'a>> {
        self.function_signature_parameters_with_context(program_id, params, None)
    }

    fn function_type_parameters(
        &self,
        program_id: program::ProgramId,
        this_param: Option<&TSThisParameter<'a>>,
        params: &FormalParameters<'a>,
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
        params: &FormalParameters<'a>,
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
        parameter: &FormalParameter<'a>,
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
        parameter: &FormalParameter<'a>,
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
        parameter: &FormalParameterRest<'a>,
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
        type_annotation: Option<&TSTypeAnnotation<'a>>,
    ) -> Ty<'a> {
        let ty = self.get_type_from_ts_type_annotation(program_id, type_annotation);
        self.get_apparent_type_at_use(program_id, ty, 0)
    }

    fn infer_function_return_type(
        &self,
        program_id: program::ProgramId,
        function: FunctionKind<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let return_type = if let FunctionKind::ArrowFunction(arrow_function) = function
            && let Some(expression) = arrow_function.get_expression()
        {
            self.get_return_expression_type(program_id, expression, node_id, false)
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
                let preserve_literal_returns = return_expressions.len() > 1;
                Ty::union(
                    self.arena(),
                    return_expressions.into_iter().map(|argument| {
                        self.get_return_expression_type(
                            program_id,
                            argument,
                            node_id,
                            preserve_literal_returns,
                        )
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

    fn get_async_function_return_type(
        &self,
        program_id: program::ProgramId,
        return_type: Ty<'a>,
    ) -> Ty<'a> {
        match self.get_global_promise_type(program_id) {
            Ty::Any => Ty::any(),
            Ty::TypeReference(reference) => {
                // TODO(correctness): TypeScript wraps async returns with Promise<Awaited<T>>.
                Ty::type_reference(self.arena(), reference.name, [return_type])
            }
            _ => Ty::type_reference(self.arena(), "Promise", [return_type]),
        }
    }

    fn get_return_expression_type(
        &self,
        program_id: program::ProgramId,
        expression: &'a Expression<'a>,
        node_id: Option<NodeId>,
        preserve_literals: bool,
    ) -> Ty<'a> {
        if preserve_literals {
            match expression {
                Expression::NumericLiteral(literal) => {
                    return self.get_type_of_numeric_literal(literal);
                }
                Expression::StringLiteral(literal) => {
                    return self.get_type_of_string_literal(literal);
                }
                Expression::BooleanLiteral(literal) => {
                    return self.get_type_of_boolean_literal(literal);
                }
                Expression::UnaryExpression(unary_expression)
                    if unary_expression.operator == UnaryOperator::UnaryNegation =>
                {
                    if let Expression::NumericLiteral(literal) = &unary_expression.argument {
                        let name = self
                            .arena()
                            .str(&format!("-{}", self.numeric_literal_name(literal)));
                        return Ty::number_literal(self.arena(), name);
                    }
                }
                _ => {}
            }
        }

        match expression {
            Expression::NewExpression(new_expression) => {
                self.get_type_of_new_expression(program_id, new_expression)
            }
            _ => self.get_type_of_expression_with_node(program_id, expression, node_id),
        }
    }

    fn get_imported_symbol(&self, symbol: SymbolRef) -> Option<SymbolRef> {
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
                let argument_type =
                    self.get_type_of_expression_with_node(program_id, &spread.argument, node_id);
                array_element_type(argument_type).unwrap_or_else(Ty::any)
            }
            ArrayExpressionElement::Elision(_) => Ty::any(),
            _ => {
                self.get_type_of_expression_with_node(program_id, element.to_expression(), node_id)
            }
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

    fn variable_declarator_for_symbol(
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
                    if declarator.kind == VariableDeclarationKind::Const
                        && !self.is_in_exported_declaration(program_id, declaration)
                    {
                        self.get_type_of_const_initializer(program_id, expression, declaration)
                    } else {
                        self.get_type_of_expression_at_node(program_id, expression, declaration)
                    }
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

        let iterable_type =
            self.get_type_of_expression_with_node(program_id, &for_of.right, Some(for_of_node_id));
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
                        .or_else(|| array_element_type(pattern_type))
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
                        array_element_type(pattern_type)
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
        parameter: &FormalParameter<'a>,
        annotation: &TSTypeAnnotation<'a>,
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
        let ty = self.get_type_of_expression_with_node(program_id, &await_expr.argument, node_id);
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
            Ty::Tuple(tuple) => Some(
                self.get_for_of_element_type(
                    program_id,
                    node_id,
                    Ty::union(
                        self.arena(),
                        tuple
                            .elements
                            .iter()
                            .map(|element| tuple_element_type(*element)),
                    ),
                    is_await,
                ),
            ),
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

    fn is_scoped_type_parameter_reference(
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

fn is_number_index_type(ty: Ty<'_>) -> bool {
    matches!(ty, Ty::Number | Ty::NumberLiteral(_))
}

fn is_promise_like_type_reference(name: &str) -> bool {
    matches!(name, "Promise" | "PromiseLike")
}

fn is_iterable_type_reference(name: &str) -> bool {
    matches!(
        name,
        "AsyncIterable"
            | "AsyncIterableIterator"
            | "AsyncIterator"
            | "AsyncIteratorObject"
            | "Iterable"
            | "IterableIterator"
            | "Iterator"
            | "IteratorObject"
            | "ArrayIterator"
            | "MapIterator"
            | "SetIterator"
    )
}

fn push_type_parameter_names<'a>(
    names: &mut Vec<&'a str>,
    type_parameters: Option<&oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
) {
    if let Some(type_parameters) = type_parameters {
        names.extend(
            type_parameters
                .params
                .iter()
                .map(|parameter| parameter.name.name.as_str()),
        );
    }
}

fn tuple_index_from_expression(expression: &Expression<'_>) -> Option<usize> {
    let Expression::NumericLiteral(literal) = expression else {
        return None;
    };
    if !literal.value.is_finite() || literal.value < 0.0 || literal.value.fract() != 0.0 {
        return None;
    }
    if literal.value > usize::MAX as f64 {
        return None;
    }
    Some(literal.value as usize)
}

fn tuple_element_type(element: TupleElement<'_>) -> Ty<'_> {
    match element {
        TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => ty,
    }
}

fn tuple_element_type_at_index<'a>(object_type: &Ty<'a>, index: usize) -> Option<Ty<'a>> {
    let Ty::Tuple(tuple) = object_type else {
        return None;
    };

    let mut current_index = 0;
    for element in &tuple.elements {
        match element {
            TupleElement::Regular(ty) | TupleElement::Optional(ty) => {
                if current_index == index {
                    return Some(*ty);
                }
                current_index += 1;
            }
            TupleElement::Rest(ty) => {
                if index >= current_index {
                    return Some(array_element_type(*ty).unwrap_or(*ty));
                }
            }
        }
    }

    Some(Ty::undefined())
}

fn array_element_type<'a>(ty: Ty<'a>) -> Option<Ty<'a>> {
    let Ty::Array(array) = ty else {
        return None;
    };
    Some(array.element_type)
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
                    self.get_type_of_boolean_literal(literal)
                } else {
                    self.get_type_of_expression_at_node(
                        node.program_id,
                        &property.value,
                        node.node_id,
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

        let ty = (|| {
            if let Some((declaration, declarator)) = self.variable_declarator_for_symbol(sym) {
                return self.get_type_of_variable_declarator(
                    sym.program_id,
                    declaration,
                    declarator,
                );
            }

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
        })();

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

    fn get_type_of_symbol_at_location(&self, node: NodeRef) -> Ty<'a> {
        self.get_type_at_location(node)
    }

    fn get_properties_of_type(&self, _t: Ty<'a>) -> Vec<SymbolRef> {
        Vec::new()
    }

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

fn index_signature_key_types<'a>(constraint: Ty<'a>) -> Option<Vec<Ty<'a>>> {
    match constraint {
        Ty::String => Some(vec![Ty::string()]),
        Ty::Number => Some(vec![Ty::number()]),
        Ty::Symbol => Some(vec![Ty::symbol()]),
        Ty::Union(union) => {
            let mut key_types = Vec::new();
            for ty in &union.types {
                let keys = index_signature_key_types(*ty)?;
                for key in keys {
                    if !key_types.contains(&key) {
                        key_types.push(key);
                    }
                }
            }
            Some(key_types)
        }
        _ => None,
    }
}

fn is_index_signature_object(ty: Ty<'_>) -> bool {
    let Ty::Object(object) = ty else {
        return false;
    };
    object.signatures.is_empty() && object.properties.is_empty() && !object.index_infos.is_empty()
}

#[cfg(feature = "bench")]
#[doc(hidden)]
pub mod benchmark_support {
    use super::{AstKind, Checker, CheckerBuilder, NodeRef, program};
    use oxc_semantic::NodeId;

    pub struct CheckPlan {
        program_id: program::ProgramId,
        queries: Vec<CheckQuery>,
    }

    #[derive(Clone, Copy)]
    enum CheckQueryKind {
        Location,
        TypeAlias,
    }

    #[derive(Clone, Copy)]
    struct CheckQuery {
        node_id: NodeId,
        kind: CheckQueryKind,
    }

    #[must_use]
    pub fn check_plan(
        store: &program::ProgramStore<'_>,
        program_id: program::ProgramId,
    ) -> CheckPlan {
        let queries = store
            .entry(program_id)
            .map(|entry| {
                entry
                    .semantic()
                    .nodes()
                    .iter_enumerated()
                    .filter_map(|(node_id, node)| {
                        let kind = match node.kind() {
                            AstKind::BindingIdentifier(_)
                            | AstKind::IdentifierReference(_)
                            | AstKind::IdentifierName(_)
                            | AstKind::TSPropertySignature(_)
                            | AstKind::TSMethodSignature(_)
                            | AstKind::TSThisParameter(_)
                            | AstKind::FormalParameter(_)
                            | AstKind::FormalParameterRest(_)
                            | AstKind::StaticMemberExpression(_)
                            | AstKind::ObjectProperty(_)
                            | AstKind::MethodDefinition(_)
                            | AstKind::PropertyDefinition(_) => CheckQueryKind::Location,
                            AstKind::TSTypeAliasDeclaration(_) => CheckQueryKind::TypeAlias,
                            _ => return None,
                        };
                        Some(CheckQuery { node_id, kind })
                    })
                    .collect()
            })
            .unwrap_or_default();

        CheckPlan {
            program_id,
            queries,
        }
    }

    /// Run checker type queries over an already parsed and semantically built program.
    ///
    /// This intentionally excludes parsing, semantic analysis, file IO, and type string rendering
    /// so Criterion benchmarks can isolate checker work.
    #[must_use]
    pub fn check_program(
        store: &program::ProgramStore<'_>,
        program_id: program::ProgramId,
    ) -> usize {
        let plan = check_plan(store, program_id);
        check_program_with_plan(store, &plan)
    }

    #[must_use]
    pub fn check_program_with_plan(store: &program::ProgramStore<'_>, plan: &CheckPlan) -> usize {
        let checker = CheckerBuilder::new().build(store);
        let Some(entry) = store.entry(plan.program_id) else {
            return 0;
        };

        plan.queries
            .iter()
            .filter_map(|query| {
                let node_ref = NodeRef::new(plan.program_id, query.node_id);
                let node = entry.semantic().nodes().kind(query.node_id);
                let ty = match node {
                    _ if matches!(query.kind, CheckQueryKind::Location) => {
                        checker.get_type_at_location(node_ref)
                    }
                    AstKind::TSTypeAliasDeclaration(alias)
                        if matches!(query.kind, CheckQueryKind::TypeAlias) =>
                    {
                        checker.get_type_of_type_alias_declaration(plan.program_id, alias)
                    }
                    _ => return None,
                };

                Some(usize::from(!ty.is_none()))
            })
            .sum()
    }
}

#[cfg(all(test, any(feature = "conformance", feature = "conformance-tsc")))]
mod conformance;

#[cfg(test)]
mod test {
    use super::*;
    use crate::program::ProgramHost;
    use oxc_allocator::Allocator;
    use oxc_str::Ident;
    use std::cell::RefCell;
    use std::{
        collections::HashMap,
        path::{Path, PathBuf},
    };

    struct TestProgramHost {
        cwd: PathBuf,
        files: HashMap<PathBuf, String>,
    }

    impl TestProgramHost {
        fn new(cwd: impl Into<PathBuf>) -> Self {
            Self {
                cwd: cwd.into(),
                files: HashMap::new(),
            }
        }

        fn add_file(mut self, path: impl AsRef<Path>, source_text: &str) -> Self {
            let path = self.canonicalize_path(path.as_ref());
            self.files.insert(path, source_text.to_string());
            self
        }
    }

    impl program::ProgramHost for TestProgramHost {
        fn read_source(&self, path: &Path) -> program::ProgramStoreResult<String> {
            self.files
                .get(&self.canonicalize_path(path))
                .cloned()
                .ok_or_else(|| program::ProgramStoreError::ReadSource {
                    path: path.to_path_buf(),
                    message: "file not found".to_string(),
                })
        }

        fn canonicalize_path(&self, path: &Path) -> PathBuf {
            if path.is_absolute() {
                path.to_path_buf()
            } else {
                self.cwd.join(path)
            }
        }

        fn resolve_module(
            &self,
            _containing_file: &Path,
            specifier: &str,
        ) -> program::HostModuleResolution {
            program::HostModuleResolution::Missing(specifier.to_string())
        }
    }

    struct ParseAndCheck<'a> {
        store: program::ProgramStore<'a>,
        program_id: program::ProgramId,
    }

    fn parse_and_check_source<'a>(
        allocator: &'a Allocator,
        source_text: &str,
    ) -> ParseAndCheck<'a> {
        let host = TestProgramHost::new("/project").add_file("/project/main.ts", source_text);
        let store = program::ProgramStoreBuilder::new(allocator, host)
            .add_root_file("/project/main.ts")
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/main.ts")).unwrap();
        assert_eq!(
            store
                .entry(program_id)
                .unwrap()
                .semantic()
                .nodes()
                .program()
                .source_text,
            source_text
        );

        ParseAndCheck { store, program_id }
    }

    fn get_global_symbol_type<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let scoping = ret
            .store
            .entry(ret.program_id)
            .unwrap()
            .semantic()
            .scoping();
        let symbol_id = scoping.get_root_binding(Ident::from(name)).unwrap();
        checker.get_type_of_symbol(SymbolRef::new(ret.program_id, symbol_id))
    }

    fn get_type_alias_type<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let alias = semantic
            .nodes()
            .iter()
            .find_map(|node| match node.kind() {
                AstKind::TSTypeAliasDeclaration(alias) if alias.id.name == Ident::from(name) => {
                    Some(alias)
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("expected type alias `{name}`"));
        checker.get_type_of_type_alias_declaration(ret.program_id, alias)
    }

    fn get_symbol_type_in_function<'a>(
        ret: &ParseAndCheck<'a>,
        func_name: &str,
        param_name: &str,
    ) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let scoping = semantic.scoping();
        let func = scoping
            .scope_descendants_from_root()
            .find(|scope_id| {
                if let AstKind::Function(func) =
                    semantic.nodes().kind(scoping.get_node_id(*scope_id))
                {
                    func.name() == Some(Ident::from(func_name))
                } else {
                    false
                }
            })
            .unwrap();
        let symbol_id = scoping.get_binding(func, Ident::from(param_name)).unwrap();
        checker.get_type_of_symbol(SymbolRef::new(ret.program_id, symbol_id))
    }

    fn get_first_symbol_type<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let scoping = semantic.scoping();
        let symbol_id = scoping
            .scope_descendants_from_root()
            .find_map(|scope_id| scoping.get_binding(scope_id, Ident::from(name)))
            .unwrap();
        checker.get_type_of_symbol(SymbolRef::new(ret.program_id, symbol_id))
    }

    fn get_global_type<'a>(
        ret: &ParseAndCheck<'a>,
        program_id: program::ProgramId,
        name: &str,
    ) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        checker.get_global_type(program_id, name)
    }

    fn get_object_property_types<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Vec<Ty<'a>> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::ObjectProperty(property)
                    if property_key_name_str(&property.key) == Some(name) =>
                {
                    Some(checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)))
                }
                _ => None,
            })
            .collect()
    }

    fn get_ts_method_signature_types(ret: &ParseAndCheck<'_>, name: &str) -> Vec<String> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::TSMethodSignature(method)
                    if property_key_name_str(&method.key) == Some(name) =>
                {
                    Some(
                        checker
                            .get_type_at_location(NodeRef::new(ret.program_id, node_id))
                            .to_type_string(),
                    )
                }
                _ => None,
            })
            .collect()
    }

    fn get_ts_property_signature_types(ret: &ParseAndCheck<'_>, name: &str) -> Vec<String> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::TSPropertySignature(property)
                    if property_key_name_str(&property.key) == Some(name) =>
                {
                    Some(
                        checker
                            .get_type_at_location(NodeRef::new(ret.program_id, node_id))
                            .to_type_string(),
                    )
                }
                _ => None,
            })
            .collect()
    }

    fn get_identifier_reference_types<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Vec<Ty<'a>> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::IdentifierReference(identifier)
                    if identifier.name == Ident::from(name) =>
                {
                    Some(checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)))
                }
                _ => None,
            })
            .collect()
    }

    fn get_static_member_expression_types<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Vec<Ty<'a>> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::StaticMemberExpression(member)
                    if member.property.name == Ident::from(name) =>
                {
                    Some(checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)))
                }
                _ => None,
            })
            .collect()
    }

    fn arena<'a>(ret: &ParseAndCheck<'a>) -> CheckerArena<'a> {
        CheckerArena::new(ret.store.allocator())
    }

    #[test]
    fn semantic_cfg_is_built_for_programs() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "if (value) { value; }");

        assert!(
            ret.store
                .entry(ret.program_id)
                .unwrap()
                .semantic()
                .cfg()
                .is_some()
        );
    }

    #[test]
    fn default_lib_provides_global_type_symbols() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const x = 1;");
        let checker = CheckerBuilder::new().build(&ret.store);

        for (name, constructor_type) in [
            ("Array", "ArrayConstructor"),
            ("Promise", "PromiseConstructor"),
            ("Map", "MapConstructor"),
            ("Set", "SetConstructor"),
            ("Symbol", "SymbolConstructor"),
            ("Object", "ObjectConstructor"),
        ] {
            assert!(
                checker
                    .get_type_symbol_for_name(ret.program_id, name)
                    .is_some(),
                "expected default lib to provide global type `{name}`"
            );
            let value_symbol = checker
                .get_value_symbol_for_name(ret.program_id, name)
                .unwrap_or_else(|| panic!("expected default lib to provide global value `{name}`"));
            assert_eq!(
                checker.get_type_of_symbol(value_symbol).to_type_string(),
                constructor_type
            );
        }
    }

    #[test]
    fn without_default_lib_has_no_global_type_symbols() {
        let allocator = Allocator::default();
        let host = TestProgramHost::new("/project").add_file("/project/main.ts", "const x = 1;");
        let store = program::ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/main.ts")
            .without_default_lib()
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/main.ts")).unwrap();
        let checker = CheckerBuilder::new().build(&store);

        assert_eq!(store.entries().len(), 1);
        assert!(
            checker
                .get_type_symbol_for_name(program_id, "Array")
                .is_none()
        );
        assert!(
            checker
                .get_value_symbol_for_name(program_id, "Array")
                .is_none()
        );
    }

    #[test]
    fn global_symbol_table_resolves_other_root_script_declarations() {
        let allocator = Allocator::default();
        let host = TestProgramHost::new("/project")
            .add_file("/project/main.ts", "const value = shared;")
            .add_file(
                "/project/globals.ts",
                "interface Shared { count: number } declare const shared: Shared;",
            );
        let store = program::ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/main.ts")
            .add_root_file("/project/globals.ts")
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/main.ts")).unwrap();
        let checker = CheckerBuilder::new().build(&store);
        let scoping = store.entry(program_id).unwrap().semantic().scoping();
        let value_symbol_id = scoping.get_root_binding(Ident::from("value")).unwrap();

        assert!(
            checker
                .get_type_symbol_for_name(program_id, "Shared")
                .is_some()
        );
        assert_eq!(
            checker
                .get_type_of_symbol(SymbolRef::new(program_id, value_symbol_id))
                .to_type_string(),
            "Shared"
        );
    }

    #[test]
    fn local_value_symbols_shadow_default_lib_globals() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const Array = 1;
        const value = Array;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "value"),
            Ty::number_literal(arena, "1")
        );
    }

    #[test]
    fn local_undefined_binding_wins_before_global_undefined_fallback() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const undefined = 1;
        const value = undefined;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "value"),
            Ty::number_literal(arena, "1")
        );
        assert_eq!(
            get_identifier_reference_types(&ret, "undefined"),
            vec![Ty::number_literal(arena, "1")]
        );
    }

    #[test]
    fn parameter_named_undefined_shadows_global_undefined() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        function shadow(undefined: number) {
            const inside = undefined;
        }
        const outside = undefined;
        ",
        );

        assert_eq!(get_first_symbol_type(&ret, "inside"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "outside"), Ty::undefined());
        assert_eq!(
            get_identifier_reference_types(&ret, "undefined"),
            vec![Ty::number(), Ty::undefined()]
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "shadow", "undefined"),
            Ty::number()
        );
    }

    #[test]
    fn value_position_global_identifiers_resolve_to_constructor_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const arrayCtor = Array;
        const promiseCtor = Promise;
        const mapCtor = Map;
        const setCtor = Set;
        const symbolCtor = Symbol;
        const objectCtor = Object;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "arrayCtor"),
            Ty::type_reference(arena, "ArrayConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "promiseCtor"),
            Ty::type_reference(arena, "PromiseConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "mapCtor"),
            Ty::type_reference(arena, "MapConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "setCtor"),
            Ty::type_reference(arena, "SetConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "symbolCtor"),
            Ty::type_reference(arena, "SymbolConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "objectCtor"),
            Ty::type_reference(arena, "ObjectConstructor", [])
        );
    }

    #[test]
    fn value_position_global_constructors_expose_members_and_construct_signatures() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const keys = Object.keys({ a: 1 });
        const values = new Array<number>(1);
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "keys"),
            Ty::array(arena, Ty::string())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "values"),
            Ty::array(arena, Ty::number())
        );
    }

    #[test]
    fn global_type_reference_locations_resolve_symbols() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type Values = Array<number>;
        type Later = Promise<string>;
        ",
        );
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();

        let type_reference_type = |name: &str| {
            let (node_id, _) = semantic
                .nodes()
                .iter_enumerated()
                .find_map(|(node_id, node)| match node.kind() {
                    AstKind::TSTypeReference(reference)
                        if matches!(
                            &reference.type_name,
                            TSTypeName::IdentifierReference(identifier)
                                if identifier.name == Ident::from(name)
                        ) =>
                    {
                        Some((node_id, reference))
                    }
                    _ => None,
                })
                .unwrap_or_else(|| panic!("expected type reference `{name}`"));
            let symbol = checker
                .get_symbol_at_location(NodeRef::new(ret.program_id, node_id))
                .unwrap_or_else(|| panic!("expected symbol for type reference `{name}`"));
            checker.get_type_of_symbol(symbol).to_type_string()
        };

        assert_eq!(type_reference_type("Array"), "ArrayConstructor");
        assert_eq!(type_reference_type("Promise"), "PromiseConstructor");
    }

    #[test]
    fn default_lib_entries_are_marked_as_lib() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const x = 1;");

        let lib_count = ret
            .store
            .entries()
            .iter()
            .filter(|entry| entry.is_lib())
            .count();
        assert_eq!(lib_count, crate::global_lib::DEFAULT_LIB_FILES.len());

        let user_entry = ret.store.entry(ret.program_id).unwrap();
        assert!(!user_entry.is_lib());
    }

    #[test]
    fn flow_narrows_truthy_if_branch() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const x: string | undefined;
        if (x) {
            x;
        } else {
            x;
        }
        ",
        );

        let reference_types = get_identifier_reference_types(&ret, "x");
        assert_eq!(reference_types.len(), 3);
        assert_eq!(
            reference_types[0],
            Ty::union(arena(&ret), [Ty::string(), Ty::undefined()])
        );
        assert_eq!(reference_types[1], Ty::string());
        assert_eq!(
            reference_types[2],
            Ty::union(arena(&ret), [Ty::string(), Ty::undefined()])
        );
    }

    #[test]
    fn flow_narrows_typeof_if_branches() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const y: string | number | boolean;
        if (typeof y === 'string') {
            y;
        } else {
            y;
        }
        ",
        );

        let reference_types = get_identifier_reference_types(&ret, "y");
        assert_eq!(reference_types.len(), 3);
        assert_eq!(
            reference_types[0],
            Ty::union(arena(&ret), [Ty::string(), Ty::number(), Ty::boolean()])
        );
        assert_eq!(reference_types[1], Ty::string());
        assert_eq!(
            reference_types[2],
            Ty::union(arena(&ret), [Ty::number(), Ty::boolean()])
        );
    }

    #[test]
    fn flow_narrows_typeof_conditional_expression_arms() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const y: string | number | boolean;
        const z = typeof y === 'string' ? y : undefined;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "z"),
            Ty::union(arena, [Ty::string(), Ty::undefined()])
        );
        assert_eq!(
            get_identifier_reference_types(&ret, "y"),
            vec![
                Ty::union(arena, [Ty::string(), Ty::number(), Ty::boolean()]),
                Ty::string(),
            ]
        );
    }

    #[test]
    fn flow_narrows_undefined_equality_conditional_expression_arms() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        function usePrevious<TData>(previous: TData | undefined, initialValue: TData) {
            const value = previous === undefined ? initialValue : previous;
        }
        ",
        );

        assert_eq!(
            get_first_symbol_type(&ret, "value").to_type_string(),
            "TData | (TData & ({} | null))"
        );
        assert_eq!(
            get_identifier_reference_types(&ret, "previous")
                .into_iter()
                .map(Ty::to_type_string)
                .collect::<Vec<_>>(),
            vec![
                "TData | undefined".to_string(),
                "TData & ({} | null)".to_string(),
            ]
        );
    }

    #[test]
    fn flow_write_invalidates_previous_narrowing() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        let y: string | number;
        if (typeof y === 'string') {
            y = 1;
            y;
        }
        ",
        );

        let reference_types = get_identifier_reference_types(&ret, "y");
        assert_eq!(reference_types.len(), 3);
        assert_eq!(
            reference_types[0],
            Ty::union(arena(&ret), [Ty::string(), Ty::number()])
        );
        assert_eq!(reference_types[1], Ty::string());
        assert_eq!(
            reference_types[2],
            Ty::union(arena(&ret), [Ty::string(), Ty::number()])
        );
    }

    #[test]
    fn flow_evolves_empty_array_locals_from_mutations() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        let values = [];
        const before = values;
        values.push(1);
        const afterPush = values;
        values[1] = 'ready';
        const afterWrite = values;
        values = [false];
        const afterReset = values;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "before"),
            Ty::array(arena, Ty::any())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "afterPush"),
            Ty::array(arena, Ty::number())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "afterWrite"),
            Ty::array(arena, Ty::union(arena, [Ty::number(), Ty::string()]))
        );
        assert_eq!(
            get_global_symbol_type(&ret, "afterReset"),
            Ty::array(arena, Ty::boolean())
        );
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn type_enum_is_pointer_sized_payload_plus_discriminant() {
        assert_eq!(std::mem::size_of::<Ty>(), 16);
    }

    #[cfg(target_pointer_width = "32")]
    #[test]
    fn type_enum_is_pointer_sized_payload_plus_discriminant() {
        assert_eq!(std::mem::size_of::<Ty>(), 8);
    }

    #[test]
    fn assignability_handles_basic_and_structural_types() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);

        assert!(relations::is_assignable_to(Ty::number(), Ty::number()));
        assert!(relations::is_assignable_to(Ty::number(), Ty::any()));
        assert!(relations::is_assignable_to(Ty::string(), Ty::unknown()));
        assert!(!relations::is_assignable_to(Ty::number(), Ty::string()));
        assert!(relations::is_assignable_to(
            Ty::number_literal(arena, "1"),
            Ty::number()
        ));
        assert!(relations::is_assignable_to(
            Ty::array(arena, Ty::number()),
            Ty::array(arena, Ty::number())
        ));

        let source = Ty::object(
            arena,
            [
                Ty::property("x", Ty::number()),
                Ty::property("y", Ty::string()),
            ],
        );
        let target = Ty::object(arena, [Ty::property("x", Ty::number())]);

        assert!(relations::is_assignable_to(source, target));
        assert!(!relations::is_assignable_to(target, source));
    }

    #[test]
    fn simple_declared_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const a: number = 1;
        const b: string = 'hello';
        const c: boolean = true;
        const d: bigint = 1n;
        const e: undefined = undefined;
        const f: null = null;
        const g: any = 1;
        const h: unknown = 1;
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "a"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "b"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "c"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "d"), Ty::bigint());
        assert_eq!(get_global_symbol_type(&ret, "e"), Ty::undefined());
        assert_eq!(get_global_symbol_type(&ret, "f"), Ty::null());
        assert_eq!(get_global_symbol_type(&ret, "g"), Ty::any());
        assert_eq!(get_global_symbol_type(&ret, "h"), Ty::unknown());
    }

    #[test]
    fn destructured_parameters_preserve_pattern_and_property_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                type BaseStreamedQueryParams<TQueryFnData> = {
                    streamFn: (context: TQueryFnData) => TQueryFnData;
                    refetchMode?: 'append' | 'reset' | 'replace';
                };
                type SimpleStreamedQueryParams<TQueryFnData> =
                    BaseStreamedQueryParams<TQueryFnData> & {
                        reducer?: never;
                        initialValue?: never;
                    };
                type ReducibleStreamedQueryParams<TQueryFnData, TData> =
                    BaseStreamedQueryParams<TQueryFnData> & {
                        reducer: (acc: TData, chunk: TQueryFnData) => TData;
                        initialValue: TData;
                    };
                type StreamedQueryParams<TQueryFnData, TData> =
                    | SimpleStreamedQueryParams<TQueryFnData>
                    | ReducibleStreamedQueryParams<TQueryFnData, TData>;

                function streamedQuery<TQueryFnData, TData>({
                    streamFn,
                    refetchMode = 'reset',
                    reducer = (items, chunk) => items,
                    initialValue = {} as TData,
                }: StreamedQueryParams<TQueryFnData, TData>): TData {
                    return initialValue;
                }
                ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "streamedQuery").to_type_string(),
            "<TQueryFnData, TData>({ streamFn, refetchMode, reducer, initialValue, }: StreamedQueryParams<TQueryFnData, TData>) => TData"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "streamFn").to_type_string(),
            "(context: TQueryFnData) => TQueryFnData"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "refetchMode").to_type_string(),
            "\"append\" | \"reset\" | \"replace\""
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "reducer").to_type_string(),
            "(acc: TData, chunk: TQueryFnData) => TData"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "initialValue").to_type_string(),
            "TData"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "items"),
            Ty::type_reference(arena(&ret), "TData", std::iter::empty())
        );
        assert_eq!(
            get_first_symbol_type(&ret, "chunk"),
            Ty::type_reference(arena(&ret), "TQueryFnData", std::iter::empty())
        );
    }

    #[test]
    fn object_literal_call_argument_contextually_types_callback_property_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                type QueryKey = readonly unknown[];

                type BaseStreamedQueryParams<TQueryFnData, TQueryKey extends QueryKey> = {
                    streamFn: () => AsyncIterable<TQueryFnData>;
                };
                type SimpleStreamedQueryParams<TQueryFnData, TQueryKey extends QueryKey> =
                    BaseStreamedQueryParams<TQueryFnData, TQueryKey> & {
                        reducer?: never;
                        initialValue?: never;
                    };
                type ReducibleStreamedQueryParams<TQueryFnData, TData, TQueryKey extends QueryKey> =
                    BaseStreamedQueryParams<TQueryFnData, TQueryKey> & {
                        reducer: (acc: TData, chunk: TQueryFnData) => TData;
                        initialValue: TData;
                    };
                type StreamedQueryParams<TQueryFnData, TData, TQueryKey extends QueryKey> =
                    | SimpleStreamedQueryParams<TQueryFnData, TQueryKey>
                    | ReducibleStreamedQueryParams<TQueryFnData, TData, TQueryKey>;

                function streamedQuery<TQueryFnData, TData, TQueryKey extends QueryKey>(
                    params: StreamedQueryParams<TQueryFnData, TData, TQueryKey>
                ): TData {
                    return params.initialValue as TData;
                }

                interface InfiniteData<TData, TPageParam = unknown> {
                    pages: Array<TData>;
                    pageParams: Array<TPageParam>;
                }

                type Todo = { id: number; title: string };
                declare const todoStream: AsyncIterable<Todo>;
                const pageParam: number = 1;

                const queryFn = streamedQuery<Todo, InfiniteData<Todo, number>, readonly ['todos']>({
                    streamFn: () => todoStream,
                    reducer: (data, todo) => ({
                        pages: [...data.pages, todo],
                        pageParams: [...data.pageParams, pageParam],
                    }),
                    initialValue: { pages: [], pageParams: [] },
                });
                ",
        );
        let arena = arena(&ret);
        let todo_type = Ty::type_reference(arena, "Todo", std::iter::empty());
        let infinite_data_type =
            Ty::type_reference(arena, "InfiniteData", [todo_type, Ty::number()]);

        assert_eq!(get_first_symbol_type(&ret, "data"), infinite_data_type);
        assert_eq!(get_first_symbol_type(&ret, "todo"), todo_type);
        assert_eq!(
            get_object_property_types(&ret, "reducer")[0].to_type_string(),
            "(data: InfiniteData<Todo, number>, todo: Todo) => { pages: Todo[]; pageParams: number[]; }"
        );
        assert!(get_object_property_types(&ret, "pages").contains(&Ty::array(arena, todo_type)));
        assert!(get_object_property_types(&ret, "pages").contains(&Ty::array(arena, Ty::never())));
        assert!(
            get_object_property_types(&ret, "pageParams").contains(&Ty::array(arena, Ty::never()))
        );
    }

    #[test]
    fn returned_function_expression_uses_annotated_return_context_for_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                type QueryFunctionContext<TQueryKey, TPageParam = never> =
                    [TPageParam] extends [never]
                        ? { queryKey: TQueryKey; pageParam?: unknown }
                        : { queryKey: TQueryKey; pageParam: TPageParam };
                type QueryFunction<T, TQueryKey, TPageParam = never> =
                    (queryContext: QueryFunctionContext<TQueryKey, TPageParam>) => T | Promise<T>;

                function makeQuery<TData, TQueryKey>(): QueryFunction<TData, TQueryKey> {
                    return async (context) => undefined as TData;
                }
                ",
        );

        assert_eq!(
            get_first_symbol_type(&ret, "context").to_type_string(),
            "{ queryKey: TQueryKey; pageParam?: unknown; }"
        );
    }

    #[test]
    fn declared_function_type_parameters_expand_conditional_alias_annotations() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                type QueryFunctionContext<TQueryKey, TPageParam = never> =
                    [TPageParam] extends [never]
                        ? { queryKey: TQueryKey; pageParam?: unknown }
                        : { queryKey: TQueryKey; pageParam: TPageParam };

                type BaseStreamedQueryParams<TQueryKey> = {
                    streamFn: (context: QueryFunctionContext<TQueryKey>) => void;
                };

                function useParams<TQueryKey>({ streamFn }: BaseStreamedQueryParams<TQueryKey>) {
                    return streamFn;
                }
                ",
        );

        assert_eq!(
            get_first_symbol_type(&ret, "context").to_type_string(),
            "{ queryKey: TQueryKey; pageParam?: unknown; }"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "useParams", "streamFn").to_type_string(),
            "(context: { queryKey: TQueryKey; pageParam?: unknown; }) => void"
        );
    }

    #[test]
    fn streamed_query_style_aliases_render_at_use_sites() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                interface Register {}
                interface QueryClient {}
                interface AbortSignal {}
                interface Error {}
                type Todo = { id: number; title: string };
                declare const dataTagSymbol: unique symbol;
                declare const dataTagErrorSymbol: unique symbol;
                type AnyDataTag = { [dataTagSymbol]: any; [dataTagErrorSymbol]: any };
                type DataTag<TType, TValue, TError> = TType extends AnyDataTag
                    ? TType
                    : TType & { [dataTagSymbol]: TValue; [dataTagErrorSymbol]: TError };
                type InferDataFromTag<TQueryFnData, TTaggedQueryKey> =
                    TTaggedQueryKey extends DataTag<unknown, infer TaggedValue, unknown>
                        ? TaggedValue
                        : TQueryFnData;
                type TodoQueryKey = DataTag<readonly [\"todos\"], Todo[], Error>;
                type TaggedTodoData = InferDataFromTag<string, TodoQueryKey>;
                type QueryKey = Register extends { queryKey: infer TQueryKey }
                    ? TQueryKey extends readonly unknown[] ? TQueryKey : readonly unknown[]
                    : readonly unknown[];
                type QueryMeta = Register extends { queryMeta: infer TQueryMeta }
                    ? TQueryMeta extends Record<string, unknown> ? TQueryMeta : Record<string, unknown>
                    : Record<string, unknown>;
                type QueryFunctionContext<TQueryKey extends QueryKey = QueryKey, TPageParam = never> =
                    [TPageParam] extends [never]
                        ? { client: QueryClient; queryKey: TQueryKey; signal: AbortSignal; meta: QueryMeta | undefined; pageParam?: unknown; direction?: unknown }
                        : { client: QueryClient; queryKey: TQueryKey; signal: AbortSignal; pageParam: TPageParam; meta: QueryMeta | undefined };
                type QueryFunction<T = unknown, TQueryKey extends QueryKey = QueryKey, TPageParam = never> =
                    (context: QueryFunctionContext<TQueryKey, TPageParam>) => T;
                type OmitKeyof<TObject, TKey extends keyof TObject, TStrictly = 'strictly'> = Omit<TObject, TKey>;
                type StreamedQueryParams<TQueryFnData, TData, TQueryKey extends QueryKey> = {
                    streamFn: (context: QueryFunctionContext<TQueryKey>) => TQueryFnData;
                    initialValue: TData;
                };
                declare const numberedContext: QueryFunctionContext<readonly [\"todos\"], number>;
                const pageParam = numberedContext.pageParam;

                function streamedQuery<
                    TQueryFnData = unknown,
                    TData = Array<TQueryFnData>,
                    TQueryKey extends QueryKey = QueryKey,
                >({ streamFn, initialValue }: StreamedQueryParams<TQueryFnData, TData, TQueryKey>): QueryFunction<TData, TQueryKey> {
                    return (context) => {
                        const signalLessContext: OmitKeyof<typeof context, 'signal'> = {
                            client: context.client,
                            meta: context.meta,
                            queryKey: context.queryKey,
                        };
                        const meta = context.meta;
                        return initialValue;
                    };
                }
                ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "streamedQuery").to_type_string(),
            "<TQueryFnData = unknown, TData = TQueryFnData[], TQueryKey extends QueryKey = readonly unknown[]>({ streamFn, initialValue, }: StreamedQueryParams<TQueryFnData, TData, TQueryKey>) => QueryFunction<TData, TQueryKey>"
        );
        assert_eq!(
            get_type_alias_type(&ret, "QueryMeta").to_type_string(),
            "{ [x: string]: unknown; }"
        );
        assert_eq!(
            get_type_alias_type(&ret, "InferDataFromTag").to_type_string(),
            "TTaggedQueryKey extends { [dataTagSymbol]: infer TaggedValue; [dataTagErrorSymbol]: unknown; } ? TaggedValue : TQueryFnData"
        );
        assert_eq!(
            get_type_alias_type(&ret, "TaggedTodoData").to_type_string(),
            "Todo[]"
        );
        assert_eq!(
            get_ts_property_signature_types(&ret, "meta"),
            vec![
                "Record<string, unknown> | undefined",
                "Record<string, unknown> | undefined",
            ]
        );
        assert_eq!(get_global_symbol_type(&ret, "pageParam"), Ty::number());
        assert_eq!(
            get_first_symbol_type(&ret, "signalLessContext").to_type_string(),
            "OmitKeyof<{ client: QueryClient; queryKey: TQueryKey; signal: AbortSignal; meta: QueryMeta | undefined; pageParam?: unknown; direction?: unknown; }, \"signal\">"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "meta").to_type_string(),
            "Record<string, unknown> | undefined"
        );
    }

    #[test]
    fn unique_symbol_types_and_type_queries_render() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const dataTagSymbol: unique symbol;
        declare const aliasValue: typeof dataTagSymbol;
        declare const tagged: { [dataTagSymbol]: any };
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "dataTagSymbol").to_type_string(),
            "unique symbol"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "aliasValue").to_type_string(),
            "typeof dataTagSymbol"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "tagged").to_type_string(),
            "{ [dataTagSymbol]: any; }"
        );

        let ret = parse_and_check_source(
            &allocator,
            "
        declare const unsetMarker: unique symbol;
        type UnsetMarker = typeof unsetMarker;
        ",
        );

        assert_eq!(
            get_type_alias_type(&ret, "UnsetMarker").to_type_string(),
            "unique symbol"
        );
    }

    #[test]
    fn global_undefined_reference_has_type_at_location() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const value = [undefined];");
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let (node_id, _) = semantic
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| match node.kind() {
                AstKind::IdentifierReference(identifier) if identifier.name == UNDEFINED_IDENT => {
                    Some((node_id, identifier))
                }
                _ => None,
            })
            .unwrap();

        assert_eq!(
            checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)),
            Ty::undefined()
        );
    }

    #[test]
    fn declared_array_types_use_array_variant() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const values: number[] = [1, 2, 3];
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "values"),
            Ty::array(arena(&ret), Ty::number())
        );
    }

    #[test]
    fn global_array_type_references_use_array_variant() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const values: Array<number> = [1, 2, 3];
        const readonlyValues: ReadonlyArray<string> = ['a'];
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "values"),
            Ty::array(arena(&ret), Ty::number())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "readonlyValues"),
            Ty::readonly_array(arena(&ret), Ty::string())
        );
    }

    #[test]
    fn array_type_references_without_default_lib_stay_type_references() {
        let allocator = Allocator::default();
        let host = TestProgramHost::new("/project").add_file(
            "/project/main.ts",
            "const values: Array<number> = [1, 2, 3];",
        );
        let store = program::ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/main.ts")
            .without_default_lib()
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/main.ts")).unwrap();
        let expected_arena = CheckerArena::new(store.allocator());
        let checker = CheckerBuilder::new().build(&store);
        let symbol_id = store
            .entry(program_id)
            .unwrap()
            .semantic()
            .scoping()
            .get_root_binding(Ident::from("values"))
            .unwrap();

        assert_eq!(
            checker.get_type_of_symbol(SymbolRef::new(program_id, symbol_id)),
            Ty::type_reference(expected_arena, "Array", [Ty::number()])
        );
    }

    #[test]
    fn declared_tuple_types_preserve_rest_and_optional_element_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const variadic: [...string[], { huh: boolean }] = ['value', { huh: true }];
        const optional: [number?] = [];
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "variadic").to_type_string(),
            "[...string[], { huh: boolean; }]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "optional").to_type_string(),
            "[(number | undefined)?]"
        );
    }

    #[test]
    fn conditional_types_resolve_concrete_branches() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const yes: number extends number ? boolean : string = true;
        const no: number extends string ? boolean : string = 'no';
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "yes"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "no"), Ty::string());
    }

    #[test]
    fn conditional_types_preserve_unresolved_generic_checks() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const value: T extends string ? number : boolean;
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value").to_type_string(),
            "T extends string ? number : boolean"
        );
    }

    #[test]
    fn infer_types_resolve_when_concrete() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const value: string extends infer U ? U : never;
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value").to_type_string(),
            "string"
        );
    }

    #[test]
    fn type_alias_declarations_expand_top_level_alias_references() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type Pick<T, K extends keyof T> = { [P in K]: T[P] };
        type Exclude<T, U> = T extends U ? never : T;
        type Omit<T, K extends keyof any> = Pick<T, Exclude<keyof T, K>>;
        type OmitKeyof<TObject, TKey extends keyof TObject> = Omit<TObject, TKey>;
        ",
        );

        assert_eq!(
            get_type_alias_type(&ret, "OmitKeyof").to_type_string(),
            "{ [P in Exclude<keyof TObject, TKey>]: TObject[P]; }"
        );
    }

    #[test]
    fn type_literal_property_signatures_preserve_optional_modifier() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type Params = { refetchMode?: "append" | "reset" };
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Params").to_type_string(),
            "{ refetchMode?: \"append\" | \"reset\"; }"
        );
    }

    #[test]
    fn optional_mapped_type_aliases_include_undefined_and_drop_empty_intersection() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type OptionalFlat<O> = {
            [K in keyof O]?: O[K]
        } & {};
        type OptionalDeep<O> = {
            [K in keyof O]?: OptionalDeep<O[K]>
        };
        type OptionalPart<O> = {
            flat: OptionalFlat<O>
            deep: OptionalDeep<O>
        };
        ",
        );

        assert_eq!(
            get_type_alias_type(&ret, "OptionalFlat").to_type_string(),
            "{ [K in keyof O]?: O[K] | undefined; }"
        );
        assert_eq!(
            get_ts_property_signature_types(&ret, "flat"),
            vec!["{ [K in keyof O]?: O[K] | undefined; }"]
        );
        assert_eq!(
            get_ts_property_signature_types(&ret, "deep"),
            vec!["OptionalDeep<O>"]
        );
    }

    #[test]
    fn tuple_wrapped_conditionals_are_not_distributive() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const value: [never] extends [never] ? string : number = 'value';
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "value"), Ty::string());
    }

    #[test]
    fn naked_type_parameter_conditionals_distribute_over_substituted_unions() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare function f<T>(): T extends string ? boolean : number;
        const value = f<string | number>();
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value"),
            Ty::union(arena(&ret), [Ty::boolean(), Ty::number()])
        );
    }

    #[test]
    fn tuple_numeric_index_access_resolves_element_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        let t: [number, string];
        let t0 = t[0];
        let t1 = t[1];
        let t2 = t[2];
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "t0"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "t1"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "t2"), Ty::undefined());
    }

    #[test]
    fn contextually_typed_boolean_object_properties_keep_literal_location_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const plain = { huh: true };
        const annotated: { huh: boolean } = { huh: true };
        type StringsThenConfig = [...string[], { huh: boolean }];
        const tupleContext: StringsThenConfig = ['value', { huh: false }];
        ",
        );

        assert_eq!(
            get_object_property_types(&ret, "huh"),
            vec![Ty::boolean(), Ty::boolean_true(), Ty::boolean_false(),]
        );
    }

    #[test]
    fn const_initializers_use_literal_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        const count = 1;
        const label = "ready";
        const enabled = true;
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "count"),
            Ty::number_literal(arena(&ret), "1")
        );
        assert_eq!(
            get_global_symbol_type(&ret, "label"),
            Ty::string_literal(arena(&ret), "\"ready\"")
        );
        assert_eq!(get_global_symbol_type(&ret, "enabled"), Ty::boolean_true());
    }

    #[test]
    fn type_strings_render_string_literals_with_double_quotes() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);

        assert_eq!(
            Ty::string_literal(arena, "expects a string literal").to_type_string(),
            "\"expects a string literal\""
        );
    }

    #[test]
    fn literal_types_participate_in_widening_expressions() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        const count = 1;
        const sum = count + 2;
        const label = "ready";
        const message = label + "!";
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "sum"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "message"), Ty::string());
    }

    #[test]
    fn simple_inferred_variable_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        let l7 = false;
        let n = 23;
        let s = 'hello';
        let b = 1n;
        let a;
        let annotated: string = 23;
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "l7"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "n"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "s"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "b"), Ty::bigint());
        assert_eq!(get_global_symbol_type(&ret, "a"), Ty::any());
        assert_eq!(get_global_symbol_type(&ret, "annotated"), Ty::string());
    }

    #[test]
    fn angle_bracket_type_assertions_use_asserted_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const x: any;
        interface Box<T = number> { value: T; }
        interface SelfDefault<T = T> { value: T; }

        const xs = <string>x;
        const xu = <unknown>x;
        const xn = <number>x;
        const xa = <any>x;
        const boxed = (<Box>x);
        const boxedValue = (<Box>x).value;
        const explicitBoxedValue = (<Box<string>>x).value;
        const selfDefaultValue = (<SelfDefault>x).value;
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "xs"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "xu"), Ty::unknown());
        assert_eq!(get_global_symbol_type(&ret, "xn"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "xa"), Ty::any());
        assert_eq!(
            get_global_symbol_type(&ret, "boxed"),
            Ty::type_reference(arena(&ret), "Box", [Ty::number()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "boxed").to_type_string(),
            "Box<number>"
        );
        assert_eq!(get_global_symbol_type(&ret, "boxedValue"), Ty::number());
        assert_eq!(
            get_global_symbol_type(&ret, "explicitBoxedValue"),
            Ty::string()
        );
        assert_eq!(get_global_symbol_type(&ret, "selfDefaultValue"), Ty::any());
    }

    #[test]
    fn generic_function_infers_type_parameters_from_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function foo<T>(x: T) {
            return x;
        }

        const x = foo(123);
        const y = foo("test");
        const z = foo(true);
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "x"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "y"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "z"), Ty::boolean());
    }

    #[test]
    fn function_overloads_select_matching_signature() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function pick(x: string): string;
        function pick(x: number): number;
        function pick(x: string | number): string | number {
            return x;
        }

        const fromString = pick("ready");
        const fromNumber = pick(123);
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "fromString"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "fromNumber"), Ty::number());
    }

    #[test]
    fn function_overloads_skip_signatures_with_too_many_type_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function pick<T>(x: T): T;
        function pick<T, U>(x: T): U;
        function pick(x: unknown): unknown {
            return x;
        }

        const value = pick<number, string>(123);
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "value"), Ty::string());
    }

    #[test]
    fn interface_method_overloads_select_matching_signature() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface Picker {
            pick(x: string): string;
            pick(x: number): number;
        }

        declare const picker: Picker;
        const fromString = picker.pick("ready");
        const fromNumber = picker.pick(123);
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "fromString"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "fromNumber"), Ty::number());
    }

    #[test]
    fn single_interface_method_signature_location_uses_function_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface PredicateArray<T> {
            every<S extends T>(predicate: (value: T) => value is S): this is readonly S[];
        }
        "#,
        );

        assert_eq!(
            get_ts_method_signature_types(&ret, "every"),
            vec![
                "<S extends T>(predicate: (value: T) => value is S) => this is readonly S[]"
                    .to_string(),
            ]
        );
    }

    #[test]
    fn merged_interface_method_signature_locations_use_overload_object_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface MapLike<K> {
            delete(key: K): boolean;
        }
        interface MapLike<K> {
            delete(key: K): boolean;
        }
        "#,
        );

        assert_eq!(
            get_ts_method_signature_types(&ret, "delete"),
            vec![
                "{ (key: K): boolean; (key: K): boolean; }".to_string(),
                "{ (key: K): boolean; (key: K): boolean; }".to_string(),
            ]
        );
    }

    #[test]
    fn type_query_alias_instantiation_resolves_intersections() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        class ErrImpl<E> {
            e!: E;
        }

        declare const Err: typeof ErrImpl & (<T>() => T);
        type ErrAlias<U> = typeof Err<U>;
        declare const e: ErrAlias<number>;
        "#,
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "Err").to_type_string(),
            "typeof ErrImpl & (<T>() => T)"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "e"),
            Ty::intersection(
                arena,
                [
                    Ty::object(
                        arena,
                        [
                            Ty::property(
                                "new ()",
                                Ty::type_reference(arena, "ErrImpl", [Ty::number()]),
                            ),
                            Ty::property(
                                "prototype",
                                Ty::type_reference(arena, "ErrImpl", [Ty::any()]),
                            ),
                        ],
                    ),
                    Ty::function(arena, [], [], Ty::number()),
                ],
            )
        );
    }

    #[test]
    fn function_return_inference_visits_body_statements() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function empty() {
        }

        function onlyBareReturns(flag: boolean) {
            if (flag) {
                return;
            }
            return;
        }

        function nestedReturnExpression(flag: boolean) {
            if (flag) {
                return 1;
            }
        }

        function bareReturnBeforeExpression(flag: boolean) {
            if (flag) {
                return;
            }
            return "ready";
        }

        function literalUnion() {
            if (Math.random() > 0.5) {
                return 2;
            }
            return 1;
        }

        function ignoresNestedFunctionReturn() {
            function inner() {
                return true;
            }
        }

        const emptyResult = empty();
        const bareResult = onlyBareReturns(true);
        const nestedResult = nestedReturnExpression(true);
        const afterBareResult = bareReturnBeforeExpression(false);
        const literalUnionResult = literalUnion();
        const nestedFunctionResult = ignoresNestedFunctionReturn();
        "#,
        );
        let arena = arena(&ret);

        assert_eq!(get_global_symbol_type(&ret, "emptyResult"), Ty::void());
        assert_eq!(get_global_symbol_type(&ret, "bareResult"), Ty::void());
        assert_eq!(get_global_symbol_type(&ret, "nestedResult"), Ty::number());
        assert_eq!(
            get_global_symbol_type(&ret, "afterBareResult"),
            Ty::string()
        );
        assert_eq!(
            get_global_symbol_type(&ret, "literalUnionResult"),
            Ty::union(
                arena,
                [
                    Ty::number_literal(arena, "2"),
                    Ty::number_literal(arena, "1"),
                ],
            )
        );
        assert_eq!(
            get_global_symbol_type(&ret, "nestedFunctionResult"),
            Ty::void()
        );
    }

    #[test]
    fn expression_bodied_arrow_function_infers_return_expression() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "var predicate = () => false;");

        assert_eq!(
            get_global_symbol_type(&ret, "predicate").to_type_string(),
            "() => boolean"
        );
    }

    #[test]
    fn async_function_inference_wraps_return_type_in_promise() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        async function returnsString() {
            return 'value';
        }

        async function empty() {}

        const returnsNumber = async () => 1;
        const stringResult = returnsString();
        const emptyResult = empty();
        const numberResult = returnsNumber();
        "#,
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "returnsString").to_type_string(),
            "() => Promise<string>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "stringResult"),
            Ty::type_reference(arena, "Promise", [Ty::string()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "emptyResult"),
            Ty::type_reference(arena, "Promise", [Ty::void()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "numberResult"),
            Ty::type_reference(arena, "Promise", [Ty::number()])
        );
    }

    #[test]
    fn await_union_and_for_await_preserve_async_iterable_element_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        async function useStream<TQueryFnData>(
            streamFn: () => AsyncIterable<TQueryFnData> | Promise<AsyncIterable<TQueryFnData>>,
        ) {
            const stream = await streamFn();
            for await (const chunk of stream) {
                chunk;
            }
        }
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "stream").to_type_string(),
            "AsyncIterable<TQueryFnData>"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "chunk").to_type_string(),
            "Awaited<TQueryFnData>"
        );
    }

    #[test]
    fn await_structural_thenable_uses_fulfilled_callback_value_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function createPromiseLike(): PromiseLike<string>;

        interface MyThenable {
            then(onFulfilled: () => void, onRejected: () => void): MyThenable;
        }

        declare function createMyThenable(): MyThenable;

        async function main() {
            const promiseLikeValue = await createPromiseLike();
            const customThenableValue = await createMyThenable();
        }
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "promiseLikeValue"),
            Ty::string()
        );
        assert_eq!(
            get_first_symbol_type(&ret, "customThenableValue"),
            Ty::never()
        );
    }

    #[test]
    fn promise_constructor_contextually_types_executor_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "const promise = new Promise((resolve, reject) => resolve('value'));",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "promise"),
            Ty::type_reference(arena, "Promise", [Ty::unknown()])
        );
        assert_eq!(
            get_first_symbol_type(&ret, "resolve").to_type_string(),
            "(value: unknown) => void"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "reject").to_type_string(),
            "(reason?: any) => void"
        );
    }

    #[test]
    fn promise_finally_returns_original_promise_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "const rejected = Promise.reject('value').finally();",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "rejected"),
            Ty::type_reference(arena(&ret), "Promise", [Ty::never()])
        );
    }

    #[test]
    fn promise_then_and_catch_infer_callback_returns_through_nullable_callback_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        async function returnsPromise() { return 'value'; }
        const thenMethod = returnsPromise().then;
        const thenResult = returnsPromise().then(() => {});
        const defaultThenResult = returnsPromise().then();
        const catchMethod = Promise.reject('value').catch;
        const catchResult = Promise.reject('value').catch(() => {});
        "#,
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "thenMethod").to_type_string(),
            "<TResult1, TResult2>(onfulfilled?: ((value: string) => TResult1 | PromiseLike<TResult1>) | null | undefined, onrejected?: ((reason: any) => TResult2 | PromiseLike<TResult2>) | null | undefined) => Promise<TResult1 | TResult2>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "thenResult"),
            Ty::type_reference(arena, "Promise", [Ty::void()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "defaultThenResult"),
            Ty::type_reference(arena, "Promise", [Ty::string()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "catchMethod").to_type_string(),
            "<TResult>(onrejected?: ((reason: any) => TResult | PromiseLike<TResult>) | null | undefined) => Promise<TResult>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "catchResult"),
            Ty::type_reference(arena, "Promise", [Ty::void()])
        );
    }

    #[test]
    fn awaited_special_handling_requires_global_awaited_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type Awaited<T> = { value: T };
        type Value = Awaited<Promise<number>>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Value").to_type_string(),
            "{ value: Promise<number>; }"
        );
    }

    #[test]
    fn global_script_function_declarations_merge_across_programs() {
        let allocator = Allocator::default();
        let host = TestProgramHost::new("/project")
            .add_file(
                "/project/a.ts",
                "async function returnsPromise() { return 'value'; }",
            )
            .add_file(
                "/project/b.ts",
                "async function returnsPromise() { return 'value'; }",
            )
            .add_file(
                "/project/e.ts",
                "async function returnsPromise() { return 'value'; }",
            );
        let store = program::ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/a.ts")
            .add_root_file("/project/b.ts")
            .add_root_file("/project/e.ts")
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/a.ts")).unwrap();
        let ret = ParseAndCheck { store, program_id };

        assert_eq!(
            get_global_symbol_type(&ret, "returnsPromise").to_type_string(),
            "{ (): Promise<string>; (): Promise<string>; (): Promise<string>; }"
        );
    }

    #[test]
    fn generic_function_uses_explicit_type_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function foo<T>(x: T) {
            return x;
        }

        const x = foo<string>("test");
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "x"), Ty::string());
    }

    #[test]
    fn generic_function_substitutes_object_return_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function box<T>(x: T) {
            return {value: x};
        }

        const x = box(123);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "x"),
            Ty::object(arena(&ret), [Ty::property("value", Ty::number())])
        );
    }

    #[test]
    fn generic_type_references_preserve_type_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type Box<T> = { value: T };

        function box<T>(x: T): Box<T> {
            return {value: x};
        }

        const explicit: Box<string> = {value: "test"};
        const inferred = box(123);
        const fromExplicitCall = box<string>("test");
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "explicit"),
            Ty::type_reference(arena(&ret), "Box", [Ty::string()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "inferred"),
            Ty::type_reference(arena(&ret), "Box", [Ty::number()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromExplicitCall"),
            Ty::type_reference(arena(&ret), "Box", [Ty::string()])
        );
    }

    #[test]
    fn generic_function_defaults_render_and_apply_when_not_inferred() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface A { a: number; }
        declare const a: A;
        declare const fn: <T = A>(x: T) => T;
        declare function foo<T = A>(x?: T): T;

        const fromDefault = foo();
        const fromInference = foo(a);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "fn").to_type_string(),
            "<T = A>(x: T) => T"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(),
            "<T = A>(x?: T) => T"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromDefault"),
            Ty::type_reference(arena(&ret), "A", std::iter::empty())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromInference"),
            Ty::type_reference(arena(&ret), "A", std::iter::empty())
        );
    }

    #[test]
    fn generic_function_constraints_render_and_apply_when_not_inferred() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface A { a: number; }
        declare const a: A;
        declare const fn: <T extends A>(x: T) => T;
        declare function foo<T extends A, U extends T = T>(x?: T, y?: U): [T, U];

        const fromConstraint = foo();
        const fromInference = foo(a);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "fn").to_type_string(),
            "<T extends A>(x: T) => T"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(),
            "<T extends A, U extends T = T>(x?: T, y?: U) => [T, U]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromConstraint").to_type_string(),
            "[A, A]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromInference").to_type_string(),
            "[A, A]"
        );
    }

    #[test]
    fn keyof_constraints_and_indexed_access_types_render() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface Window {}
        interface WindowEventMap {}
        declare const source: {
            <K extends keyof WindowEventMap>(type: K, listener: (this: Window, ev: WindowEventMap[K]) => any): void;
        };
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "source").to_type_string(),
            "{ <K extends keyof WindowEventMap>(type: K, listener: (this: Window, ev: WindowEventMap[K]) => any): void; }"
        );
    }

    #[test]
    fn new_expression_infers_class_instance_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        class Foo {
            doThing(x: {a: number}) {
                return {b: x.a};
            }
        }
        const c = new Foo();
        const x = c.doThing({a: 12});
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "c"),
            Ty::type_reference(arena(&ret), "Foo", std::iter::empty())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "x"),
            Ty::object(arena(&ret), [Ty::property("b", Ty::number())])
        );
    }

    #[test]
    fn class_properties_are_available_on_instances_statics_and_this() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        class Item {
            name: string = "item";
        }

        class Example {
            ready: boolean = false;
            count = 1;
            item: Item = new Item();
            static enabled: boolean = true;

            getReady() {
                return this.ready;
            }

            getCount() {
                return this.count;
            }

            getItemName() {
                return this.item.name;
            }

            static getEnabled() {
                return Example.enabled;
            }
        }

        const instance = new Example();
        const ready = instance.ready;
        const count = instance.count;
        const itemName = instance.item.name;
        const readyFromThis = instance.getReady();
        const countFromThis = instance.getCount();
        const nameFromThis = instance.getItemName();
        const enabled = Example.enabled;
        const enabledFromMethod = Example.getEnabled();
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "ready"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "count"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "itemName"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "readyFromThis"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "countFromThis"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "nameFromThis"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "enabled"), Ty::boolean());
        assert_eq!(
            get_global_symbol_type(&ret, "enabledFromMethod"),
            Ty::boolean()
        );
    }

    #[test]
    fn array_every_contextually_types_callback_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        class Ship {
            isSunk: boolean = false;
        }

        class Board {
            ships: Ship[] = [];

            allShipsSunk() {
                return this.ships.every(function (val) {
                    return val.isSunk;
                });
            }
        }

        const board = new Board();
        const sunk = board.allShipsSunk();
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "val"),
            Ty::type_reference(arena(&ret), "Ship", std::iter::empty())
        );
        assert_eq!(get_global_symbol_type(&ret, "sunk"), Ty::boolean());
    }

    #[test]
    fn array_map_infers_async_callback_return_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const mapped = [1, 2, 3].map(async x => x + 1);
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "mapped"),
            Ty::array(arena, Ty::type_reference(arena, "Promise", [Ty::number()]))
        );
        assert_eq!(get_first_symbol_type(&ret, "x"), Ty::number());
    }

    #[test]
    fn array_map_string_callback_member_uses_global_string_interface() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const lengths = ['a', 'bb', 'ccc'].map(x => x.length);
        ",
        );
        let arena = arena(&ret);

        assert_eq!(get_first_symbol_type(&ret, "x"), Ty::string());
        assert_eq!(
            get_static_member_expression_types(&ret, "length"),
            vec![Ty::number()]
        );
        assert_eq!(
            get_global_symbol_type(&ret, "lengths"),
            Ty::array(arena, Ty::number())
        );
    }

    #[test]
    fn primitive_and_object_members_use_global_interfaces() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const key: symbol;
        declare const big: bigint;
        const objectText = ({ a: 1 }).toString();
        const functionLength = ((value: number) => value).length;
        const fixed = (1).toFixed();
        const boolValue = (true).valueOf();
        const symbolText = key.toString();
        const bigValue = big.valueOf();
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "objectText"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "functionLength"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "fixed"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "boolValue"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "symbolText"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "bigValue"), Ty::bigint());
    }

    #[test]
    fn function_parameter_declared_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "function foo(a: number, b: string, c: boolean) {}",
        );

        assert_eq!(get_symbol_type_in_function(&ret, "foo", "a"), Ty::number());
        assert_eq!(get_symbol_type_in_function(&ret, "foo", "b"), Ty::string());
        assert_eq!(get_symbol_type_in_function(&ret, "foo", "c"), Ty::boolean());
    }

    #[test]
    fn optional_function_parameters_render_optional_in_signatures() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "declare function foo(a?: number): number;");

        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(),
            "(a?: number) => number"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "foo", "a"),
            Ty::union(arena(&ret), [Ty::number(), Ty::undefined()])
        );
    }

    #[test]
    fn rest_function_parameters_render_in_signatures() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "function foo(a: string, b?: string, c?: number, ...d: number[]) {}",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(),
            "(a: string, b?: string, c?: number, ...d: number[]) => void"
        );
        let Ty::Function(function) = get_global_symbol_type(&ret, "foo") else {
            panic!("expected function type");
        };
        let rest_parameter = function.parameters[3];
        assert_eq!(rest_parameter.name, "d");
        assert!(rest_parameter.rest);
    }

    #[test]
    fn function_type_annotations_resolve_to_function_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "declare function pipe<A extends any[], B>(ab: (...args: A) => B): B;",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_first_symbol_type(&ret, "ab"),
            Ty::function(
                arena,
                [],
                [Ty::rest_parameter(
                    arena.str("args"),
                    Ty::type_reference(arena, arena.str("A"), []),
                )],
                Ty::type_reference(arena, arena.str("B"), []),
            )
        );
    }

    #[test]
    fn function_type_predicates_render_in_signatures() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
declare function acceptsPredicate<T, S extends T>(
    predicate: (value: T) => value is S,
    assertion: (value: unknown) => asserts value is string,
): void;
"#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "predicate").to_type_string(),
            "(value: T) => value is S"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "assertion").to_type_string(),
            "(value: unknown) => asserts value is string"
        );
    }

    #[test]
    fn test_get_global_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "");
        let checker = CheckerBuilder::new().build(&ret.store);

        // Now test things that should be in the global environment:
        assert_eq!(
            get_global_type(&ret, ret.program_id, "Promise"),
            Ty::type_reference(arena(&ret), "Promise", std::iter::empty())
        );
        assert_eq!(
            checker.get_global_promise_type(ret.program_id),
            Ty::type_reference(arena(&ret), "Promise", std::iter::empty())
        );
    }
}
