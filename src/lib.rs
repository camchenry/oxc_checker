#![allow(dead_code, unused_imports)]
use oxc_allocator::Allocator;
use oxc_ast::{
    AstKind,
    ast::{
        ArrayExpression, ArrayExpressionElement, BinaryExpression, BindingPattern, BooleanLiteral,
        CallExpression, Class, ClassElement, Expression, FormalParameter, Function,
        MethodDefinition, MethodDefinitionKind, NewExpression, NumericLiteral, ObjectExpression,
        ObjectPropertyKind, Program, PropertyDefinition, PropertyKey, Statement,
        StaticMemberExpression, StringLiteral, TSSignature, TSType, TSTypeAnnotation, TSTypeName,
        TSTypeReference, UnaryExpression, VariableDeclarationKind, VariableDeclarator,
    },
};
use oxc_index::nonmax::NonMaxU32;
use oxc_semantic::{AstNode, AstNodes, NodeId, Semantic, SemanticBuilder, SymbolId};
use oxc_span::{GetSpan, Span};
use oxc_str::{Ident, static_ident};
use oxc_syntax::operator::{BinaryOperator, UnaryOperator};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

pub mod program;
mod relations;
mod types;

use types::*;

const UNDEFINED_IDENT: Ident = static_ident!("undefined");

fn infer_type_parameter_from_types<'a>(
    parameter_type: &Ty<'a>,
    argument_type: &Ty<'a>,
    type_parameters: &[&'a str],
    substitutions: &mut HashMap<&'a str, Ty<'a>>,
) {
    match (parameter_type, argument_type) {
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
                if let Some(argument_property) = argument_object
                    .properties
                    .iter()
                    .find(|argument_property| argument_property.name == parameter_property.name)
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
        _ => {}
    }
}

fn property_key_name(key: &PropertyKey<'_>) -> Option<String> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.name.to_string()),
        _ => None,
    }
}

fn property_key_name_str<'a>(key: &PropertyKey<'a>) -> Option<&'a str> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.name.as_str()),
        _ => None,
    }
}

fn property_key_span(key: &PropertyKey<'_>) -> Option<Span> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.span),
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
    fn get_signatures_of_type(&self, t: Ty<'a>, kind: SignatureKind) -> Vec<Signature>;
    fn get_index_infos_of_type(&self, t: Ty<'a>) -> Vec<IndexInfo>;
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
        expression: &Expression<'a>,
    ) -> Ty<'a> {
        self.get_type_of_expression_with_node(program_id, expression, None)
    }

    fn get_type_of_expression_at_node(
        &self,
        program_id: program::ProgramId,
        expression: &Expression<'a>,
        node_id: NodeId,
    ) -> Ty<'a> {
        self.get_type_of_expression_with_node(program_id, expression, Some(node_id))
    }

    /// Resolve an expression type with a semantic context node when ancestor context is needed.
    /// This keeps `this` and member expressions tied to the class or call site they appear in.
    fn get_type_of_expression_with_node(
        &self,
        program_id: program::ProgramId,
        expression: &Expression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        match expression {
            Expression::Identifier(identifier) => {
                // TODO: I think we actually need to check if this is the *global* `undefined` reference,
                // but for now we'll just assume it's always the global one.
                if identifier.name == UNDEFINED_IDENT {
                    return Ty::undefined();
                }
                identifier
                    .reference_id
                    .get()
                    .and_then(|reference_id| {
                        self.semantic(program_id)
                            .scoping()
                            .get_reference(reference_id)
                            .symbol_id()
                    })
                    .map_or_else(Ty::any, |symbol_id| {
                        self.get_type_of_symbol(SymbolRef::new(program_id, symbol_id))
                    })
            }
            Expression::ObjectExpression(object) => {
                self.get_type_of_object_expression(program_id, object, node_id)
            }
            Expression::BinaryExpression(binary_expression) => {
                self.get_type_of_binary_expression(program_id, binary_expression, node_id)
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
            Expression::StaticMemberExpression(member) => {
                self.get_type_of_static_member_expression(program_id, member, node_id)
            }
            Expression::ThisExpression(_) => node_id
                .and_then(|node_id| self.get_enclosing_class_instance_type(program_id, node_id))
                .unwrap_or_else(Ty::any),
            Expression::FunctionExpression(function) => {
                self.get_type_of_function_signature_with_node(program_id, function, node_id)
            }
            Expression::NullLiteral(_) => Ty::null(),
            _ => Ty::from_expression(expression),
        }
    }

    fn get_type_of_const_initializer(
        &self,
        program_id: program::ProgramId,
        expression: &Expression<'a>,
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
        Ty::boolean_literal(self.arena(), literal.value)
    }

    fn get_type_of_binary_expression(
        &self,
        program_id: program::ProgramId,
        binary_expression: &BinaryExpression<'a>,
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

    fn get_type_of_unary_expression(
        &self,
        program_id: program::ProgramId,
        unary_expression: &UnaryExpression<'a>,
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
        matches!(
            ty,
            Ty::Number
                | Ty::Literal(types::TyLiteral {
                    primitive: types::TyLiteralPrimitiveType::Number,
                    ..
                })
        )
    }

    fn is_string_like_for_addition(&self, ty: Ty<'a>) -> bool {
        matches!(
            ty,
            Ty::String
                | Ty::Literal(types::TyLiteral {
                    primitive: types::TyLiteralPrimitiveType::String,
                    ..
                })
        )
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
        object: &ObjectExpression<'a>,
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
        member: &StaticMemberExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let object_type =
            self.get_type_of_expression_with_node(program_id, &member.object, node_id);
        object_type
            .property_type(member.property.name.as_str())
            .or_else(|| self.get_array_property_type(&object_type, member.property.name.as_str()))
            .or_else(|| {
                self.get_property_type_of_named_type(
                    program_id,
                    &object_type,
                    member.property.name.as_str(),
                )
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
                                member.property.name.as_str(),
                            )
                        })
                } else {
                    None
                }
            })
            .unwrap_or_else(Ty::any)
    }

    /// Resolve known properties on array-like types without loading TypeScript library declarations.
    /// These signatures provide enough structure for method calls to contextually type callbacks.
    fn get_array_property_type(&self, object_type: &Ty<'a>, property_name: &str) -> Option<Ty<'a>> {
        let element_type = self.get_array_element_type(object_type)?;
        match property_name {
            "every" => {
                let predicate = Ty::function(
                    self.arena(),
                    [],
                    [
                        Ty::parameter("value", element_type),
                        Ty::parameter("index", Ty::number()),
                        Ty::parameter("array", *object_type),
                    ],
                    Ty::unknown(),
                );
                Some(Ty::function(
                    self.arena(),
                    [],
                    [
                        Ty::parameter("predicate", predicate),
                        Ty::parameter("thisArg", Ty::any()),
                    ],
                    Ty::boolean(),
                ))
            }
            _ => None,
        }
    }

    /// Extract the element type from an array type.
    /// Array method signatures need this to expose callback parameter and array argument types.
    fn get_array_element_type(&self, object_type: &Ty<'a>) -> Option<Ty<'a>> {
        let Ty::Array(array) = object_type else {
            return None;
        };
        Some(array.element_type)
    }

    fn get_type_of_call_expression(
        &self,
        program_id: program::ProgramId,
        call_expression: &CallExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        match self.get_type_of_expression_with_node(program_id, &call_expression.callee, node_id) {
            Ty::Function(function) => {
                if function.type_parameters.is_empty() {
                    return function.return_type;
                }

                let mut substitutions = HashMap::new();
                let mut explicit_type_parameters = Vec::new();

                if let Some(type_arguments) = &call_expression.type_arguments {
                    for (type_parameter, type_argument) in function
                        .type_parameters
                        .iter()
                        .zip(type_arguments.params.iter())
                    {
                        substitutions.insert(
                            *type_parameter,
                            Ty::from_ts_type(self.arena(), type_argument),
                        );
                        explicit_type_parameters.push(*type_parameter);
                    }
                }

                let inferable_type_parameters = function
                    .type_parameters
                    .iter()
                    .filter(|type_parameter| !explicit_type_parameters.contains(type_parameter))
                    .cloned()
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

                function
                    .return_type
                    .substitute_type_parameters(self.arena(), &substitutions)
            }
            _ => Ty::any(),
        }
    }

    fn get_type_of_new_expression(
        &self,
        program_id: program::ProgramId,
        new_expression: &NewExpression<'a>,
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
            .map(|symbol_id| self.get_type_of_symbol(SymbolRef::new(program_id, symbol_id)));

        if let Some(Ty::TypeReference(reference)) = constructor_type
            && reference.type_arguments.is_empty()
            && let Some(instance_name) = reference.name.strip_prefix("typeof ")
        {
            return Ty::type_reference(
                self.arena(),
                self.arena().str(instance_name),
                std::iter::empty(),
            );
        }

        Ty::type_reference(self.arena(), identifier.name.as_str(), std::iter::empty())
    }

    fn get_property_type_of_named_type(
        &self,
        program_id: program::ProgramId,
        object_type: &Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let type_name = match object_type {
            Ty::TypeReference(reference) => reference.name,
            _ => return None,
        };
        let is_static = type_name.starts_with("typeof ");
        let class_name = type_name.strip_prefix("typeof ").unwrap_or(type_name);
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

    fn get_class_for_symbol(&self, symbol: SymbolRef) -> Option<(NodeId, &'a Class<'a>)> {
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        match self.nodes(symbol.program_id).kind(declaration) {
            AstKind::Class(class) => Some((declaration, class)),
            AstKind::BindingIdentifier(_) => {
                let parent_id = self.nodes(symbol.program_id).parent_id(declaration);
                if let AstKind::Class(class) = self.nodes(symbol.program_id).kind(parent_id) {
                    Some((parent_id, class))
                } else {
                    None
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
        method: &MethodDefinition<'a>,
        class_node_id: NodeId,
    ) -> Ty<'a> {
        debug_assert!(matches!(
            self.semantic(program_id).nodes().kind(class_node_id),
            AstKind::Class(_),
        ));

        let inferred_method_type = self.get_type_of_function_signature_with_node(
            program_id,
            &method.value,
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
        property: &PropertyDefinition<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        property.type_annotation.as_deref().map_or_else(
            || {
                property.value.as_ref().map_or_else(Ty::any, |value| {
                    self.get_type_of_expression_with_node(program_id, value, node_id)
                })
            },
            |annotation| Ty::from_ts_type_annotation(self.arena(), Some(annotation)),
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
                    _ => None,
                })?;

        let call_expression =
            nodes
                .ancestors(parameter_node_id)
                .find_map(|node| match node.kind() {
                    AstKind::CallExpression(call_expression) => Some(call_expression),
                    _ => None,
                })?;
        let argument_index = call_expression.arguments.iter().position(|argument| {
            argument
                .as_expression()
                .is_some_and(|expression| expression.span() == function_span)
        })?;

        let Ty::Function(callee_function) = self.get_type_of_expression_with_node(
            program_id,
            &call_expression.callee,
            Some(parameter_node_id),
        ) else {
            return None;
        };
        let Ty::Function(callback_function) = callee_function
            .parameters
            .get(argument_index)
            .map(|parameter| parameter.ty)?
        else {
            return None;
        };
        callback_function
            .parameters
            .get(parameter_index)
            .map(|parameter| parameter.ty)
    }

    fn get_type_of_function_signature(
        &self,
        program_id: program::ProgramId,
        function: &Function<'a>,
    ) -> Ty<'a> {
        self.get_type_of_function_signature_with_node(program_id, function, None)
    }

    fn get_type_of_function_signature_with_node(
        &self,
        program_id: program::ProgramId,
        function: &Function<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let type_parameters = function
            .type_parameters
            .as_ref()
            .map_or_else(Vec::new, |params| {
                params
                    .params
                    .iter()
                    .map(|parameter| parameter.name.name.as_str())
                    .collect()
            });
        let parameters = function
            .params
            .items
            .iter()
            .map(|parameter| {
                let name = binding_pattern_name_str(&parameter.pattern).unwrap_or("_");
                let ty =
                    Ty::from_ts_type_annotation(self.arena(), parameter.type_annotation.as_deref());
                Ty::parameter(name, ty)
            })
            .collect::<Vec<_>>();
        let return_type = function.return_type.as_deref().map_or_else(
            || self.infer_function_return_type(program_id, function, node_id),
            |annotation| Ty::from_ts_type_annotation(self.arena(), Some(annotation)),
        );

        Ty::function(self.arena(), type_parameters, parameters, return_type)
    }

    fn infer_function_return_type(
        &self,
        program_id: program::ProgramId,
        function: &Function<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        let Some(body) = &function.body else {
            return Ty::any();
        };
        // `function() { }` implies void return type
        if body.statements.is_empty() {
            return Ty::void();
        }
        body.statements
            .iter()
            .find_map(|statement| {
                let Statement::ReturnStatement(statement) = statement else {
                    return None;
                };
                statement
                    .argument
                    .as_ref()
                    .map(|argument| self.get_return_expression_type(program_id, argument, node_id))
            })
            .unwrap_or_else(Ty::undefined)
    }

    fn get_return_expression_type(
        &self,
        program_id: program::ProgramId,
        expression: &Expression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
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
        let AstKind::ImportSpecifier(specifier) = self.node_kind(declaration_ref) else {
            return None;
        };
        let AstKind::ImportDeclaration(import_declaration) =
            self.nodes(symbol.program_id).parent_kind(declaration)
        else {
            return None;
        };
        let imported_name = specifier.imported.name();
        let imported_program_id = self
            .store
            .resolved_module(symbol.program_id, import_declaration.source.value.as_str())?;
        let imported_entry = self.store.entry(imported_program_id)?;
        let imported_symbol_id = imported_entry
            .semantic()
            .scoping()
            .get_root_binding(Ident::from(imported_name.as_str()))?;

        Some(SymbolRef::new(imported_program_id, imported_symbol_id))
    }

    fn get_type_of_import_symbol(&self, symbol: SymbolRef) -> Option<Ty<'a>> {
        self.get_imported_symbol(symbol)
            .map(|imported_symbol| self.get_type_of_symbol(imported_symbol))
    }

    fn get_type_of_array_expression(
        &self,
        program_id: program::ProgramId,
        array_expression: &ArrayExpression<'a>,
        node_id: Option<NodeId>,
    ) -> Ty<'a> {
        match array_expression.elements.len() {
            // For 0 elements: infer `any[]`
            0 => Ty::array(self.arena, Ty::any()),
            // For 1 element: infer the type of the first element
            1 => {
                let first_element = &array_expression.elements[0];
                let element_type = match first_element {
                    ArrayExpressionElement::SpreadElement(_)
                    | ArrayExpressionElement::Elision(_) => Ty::any(),
                    _ => self.get_type_of_expression_with_node(
                        program_id,
                        first_element.to_expression(),
                        node_id,
                    ),
                };
                Ty::array(self.arena, element_type)
            }
            // For 2+ elements: try to create a union type if there are mixed types
            _ => {
                // TODO(perf): avoid allocating here somehow?
                let mut element_types = Vec::default();
                for element in &array_expression.elements {
                    let element_type = match element {
                        ArrayExpressionElement::SpreadElement(_)
                        | ArrayExpressionElement::Elision(_) => Ty::any(),
                        _ => self.get_type_of_expression_with_node(
                            program_id,
                            element.to_expression(),
                            node_id,
                        ),
                    };
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
}

impl<'a> Checker<'a> for CheckerReturn<'a, '_> {
    fn get_symbol_at_location(&self, node: NodeRef) -> Option<SymbolRef> {
        match self.node_kind(node) {
            AstKind::BindingIdentifier(identifier) => identifier
                .symbol_id
                .get()
                .map(|symbol_id| SymbolRef::new(node.program_id, symbol_id)),
            AstKind::IdentifierReference(identifier) => {
                identifier.reference_id.get().and_then(|reference_id| {
                    self.semantic(node.program_id)
                        .scoping()
                        .get_reference(reference_id)
                        .symbol_id()
                        .map(|symbol_id| SymbolRef::new(node.program_id, symbol_id))
                })
            }
            _ => None,
        }
    }

    fn get_type_at_location(&self, node: NodeRef) -> Ty<'a> {
        match self.node_kind(node) {
            AstKind::IdentifierReference(identifier) if identifier.name == UNDEFINED_IDENT => {
                Ty::undefined()
            }
            AstKind::TSPropertySignature(property) => {
                Ty::from_ts_type_annotation(self.arena(), property.type_annotation.as_deref())
            }
            AstKind::ObjectProperty(property) => {
                self.get_type_of_expression_at_node(node.program_id, &property.value, node.node_id)
            }
            AstKind::StaticMemberExpression(member) => self.get_type_of_static_member_expression(
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
            _ => self
                .get_symbol_at_location(node)
                .map_or_else(Ty::none, |sym| self.get_type_of_symbol(sym)),
        }
    }

    fn get_declared_type_of_symbol(&self, sym: SymbolRef) -> Ty<'a> {
        let declaration = self
            .semantic(sym.program_id)
            .scoping()
            .symbol_declaration(sym.symbol_id);
        match self.nodes(sym.program_id).kind(declaration) {
            AstKind::VariableDeclarator(declarator) => {
                Ty::from_ts_type_annotation(self.arena(), declarator.type_annotation.as_deref())
            }
            AstKind::FormalParameter(parameter) => {
                parameter.type_annotation.as_deref().map_or_else(
                    || {
                        self.get_contextual_type_of_formal_parameter(
                            sym.program_id,
                            declaration,
                            parameter,
                        )
                        .unwrap_or_else(Ty::any)
                    },
                    |annotation| Ty::from_ts_type_annotation(self.arena(), Some(annotation)),
                )
            }
            AstKind::FormalParameterRest(parameter) => {
                Ty::from_ts_type_annotation(self.arena(), parameter.type_annotation.as_deref())
            }
            AstKind::CatchParameter(parameter) => {
                Ty::from_ts_type_annotation(self.arena(), parameter.type_annotation.as_deref())
            }
            AstKind::PropertyDefinition(property) => {
                self.get_type_of_property_definition(sym.program_id, property, Some(declaration))
            }
            AstKind::Function(function) => self.get_type_of_function_signature_with_node(
                sym.program_id,
                function,
                Some(declaration),
            ),
            AstKind::AccessorProperty(property) => {
                Ty::from_ts_type_annotation(self.arena(), property.type_annotation.as_deref())
            }
            AstKind::BindingIdentifier(identifier) => {
                match self.nodes(sym.program_id).parent_kind(declaration) {
                    AstKind::Class(_) => {
                        let name = self
                            .arena()
                            .concat_strs_array(["typeof ", identifier.name.as_str()]);
                        Ty::type_reference(self.arena(), name, std::iter::empty())
                    }
                    AstKind::Function(function) => self.get_type_of_function_signature_with_node(
                        sym.program_id,
                        function,
                        Some(declaration),
                    ),
                    _ => Ty::none(),
                }
            }
            AstKind::Class(class) => class.id.as_ref().map_or_else(Ty::any, |identifier| {
                let name = self
                    .arena()
                    .concat_strs_array(["typeof ", identifier.name.as_str()]);
                Ty::type_reference(self.arena(), name, std::iter::empty())
            }),
            _ => Ty::none(),
        }
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
                    if declarator.type_annotation.is_some() {
                        Ty::from_ts_type_annotation(
                            self.arena(),
                            declarator.type_annotation.as_deref(),
                        )
                    } else {
                        declarator.init.as_ref().map_or_else(Ty::any, |expression| {
                            let declaration = self
                                .semantic(sym.program_id)
                                .scoping()
                                .symbol_declaration(sym.symbol_id);
                            if declarator.kind == VariableDeclarationKind::Const
                                && !self.is_in_exported_declaration(sym.program_id, declaration)
                            {
                                self.get_type_of_const_initializer(
                                    sym.program_id,
                                    expression,
                                    declaration,
                                )
                            } else {
                                self.get_type_of_expression_at_node(
                                    sym.program_id,
                                    expression,
                                    declaration,
                                )
                            }
                        })
                    }
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

    fn get_signatures_of_type(&self, _t: Ty<'a>, _kind: SignatureKind) -> Vec<Signature> {
        Vec::new()
    }

    fn get_index_infos_of_type(&self, _t: Ty<'a>) -> Vec<IndexInfo> {
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

    fn arena<'a>(ret: &ParseAndCheck<'a>) -> CheckerArena<'a> {
        CheckerArena::new(ret.store.allocator())
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
        assert_eq!(
            get_global_symbol_type(&ret, "enabled"),
            Ty::boolean_true(arena(&ret))
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
                [Ty::parameter(
                    arena.str("...args"),
                    Ty::type_reference(arena, arena.str("A"), []),
                )],
                Ty::type_reference(arena, arena.str("B"), []),
            )
        );
    }
}
