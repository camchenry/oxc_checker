#![allow(dead_code, unused_imports)]
use oxc_allocator::{Allocator, Vec as ArenaVec};
use oxc_ast::{
    AstKind,
    ast::{
        BindingPattern, CallExpression, Class, ClassElement, Expression, Function, NewExpression,
        ObjectExpression, ObjectPropertyKind, Program, PropertyKey, Statement,
        StaticMemberExpression, TSSignature, TSType, TSTypeAnnotation, TSTypeName, TSTypeReference,
        VariableDeclarator,
    },
};
use oxc_index::nonmax::NonMaxU32;
use oxc_semantic::{AstNode, AstNodes, NodeId, Semantic, SemanticBuilder, SymbolId};
use oxc_span::{GetSpan, Span};
use oxc_str::Ident;
use std::{cell::RefCell, collections::HashMap};

pub mod program;

#[derive(Clone, Copy)]
struct CheckerArena<'a> {
    allocator: &'a Allocator,
}

impl<'a> CheckerArena<'a> {
    fn new(allocator: &'a Allocator) -> Self {
        Self { allocator }
    }

    fn alloc<T>(&self, value: T) -> &'a T {
        self.allocator.alloc(value)
    }

    fn str(&self, value: &str) -> &'a str {
        self.allocator.alloc_str(value)
    }

    fn concat_strs_array<const N: usize>(&self, strings: [&str; N]) -> &'a str {
        self.allocator.alloc_concat_strs_array(strings)
    }

    fn vec_from_iter<T>(&self, iter: impl IntoIterator<Item = T>) -> ArenaVec<'a, T> {
        ArenaVec::from_iter_in(iter, self.allocator)
    }
}

#[repr(C, u8)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Ty<'a> {
    None,
    Number,
    String,
    Boolean,
    Bigint,
    Undefined,
    Null,
    Any,
    Unknown,
    Object(&'a TyObject<'a>),
    Function(&'a TyFunction<'a>),
    TypeReference(&'a TyTypeReference<'a>),
    Type(&'a TyType<'a>),
}

#[derive(Debug, PartialEq, Eq)]
struct TyObject<'a> {
    properties: ArenaVec<'a, TyProperty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct TyProperty<'a> {
    name: &'a str,
    ty: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
struct TyFunction<'a> {
    type_parameters: ArenaVec<'a, &'a str>,
    parameters: ArenaVec<'a, TyParameter<'a>>,
    return_type: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct TyParameter<'a> {
    name: &'a str,
    ty: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
struct TyTypeReference<'a> {
    name: &'a str,
    type_arguments: ArenaVec<'a, Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct TyType<'a> {
    name: &'a str,
}

impl<'a> Ty<'a> {
    fn none() -> Self {
        Self::None
    }

    fn number() -> Self {
        Self::Number
    }

    fn string() -> Self {
        Self::String
    }

    fn boolean() -> Self {
        Self::Boolean
    }

    fn bigint() -> Self {
        Self::Bigint
    }

    fn undefined() -> Self {
        Self::Undefined
    }

    fn null() -> Self {
        Self::Null
    }

    fn any() -> Self {
        Self::Any
    }

    fn unknown() -> Self {
        Self::Unknown
    }

    fn property(name: &'a str, ty: Ty<'a>) -> TyProperty<'a> {
        TyProperty { name, ty }
    }

    fn parameter(name: &'a str, ty: Ty<'a>) -> TyParameter<'a> {
        TyParameter { name, ty }
    }

    fn object(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
    ) -> Self {
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(properties),
        }))
    }

    fn function(
        arena: CheckerArena<'a>,
        type_parameters: impl IntoIterator<Item = &'a str>,
        parameters: impl IntoIterator<Item = TyParameter<'a>>,
        return_type: Ty<'a>,
    ) -> Self {
        Self::Function(arena.alloc(TyFunction {
            type_parameters: arena.vec_from_iter(type_parameters),
            parameters: arena.vec_from_iter(parameters),
            return_type,
        }))
    }

    fn type_reference(
        arena: CheckerArena<'a>,
        name: &'a str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        Self::TypeReference(arena.alloc(TyTypeReference {
            name,
            type_arguments: arena.vec_from_iter(type_arguments),
        }))
    }

    fn type_(arena: CheckerArena<'a>, name: &'a str) -> Self {
        Self::Type(arena.alloc(TyType { name }))
    }

    fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }

    /// Take a type annotation like `: number` and return the corresponding type. Returns no
    /// type if there is no type annotation.
    fn from_ts_type_annotation(
        arena: CheckerArena<'a>,
        type_annotation: Option<&TSTypeAnnotation<'a>>,
    ) -> Self {
        type_annotation.map_or_else(Self::any, |type_annotation| {
            Self::from_ts_type(arena, &type_annotation.type_annotation)
        })
    }

    /// Turns a declared type in the AST and turns it into an actual type.
    fn from_ts_type(arena: CheckerArena<'a>, t: &TSType<'a>) -> Self {
        match t {
            TSType::TSNumberKeyword(_) => Self::number(),
            TSType::TSStringKeyword(_) => Self::string(),
            TSType::TSBooleanKeyword(_) => Self::boolean(),
            TSType::TSBigIntKeyword(_) => Self::bigint(),
            TSType::TSUndefinedKeyword(_) => Self::undefined(),
            TSType::TSNullKeyword(_) => Self::null(),
            TSType::TSAnyKeyword(_) => Self::any(),
            TSType::TSUnknownKeyword(_) => Self::unknown(),
            TSType::TSTypeLiteral(type_literal) => Self::object(
                arena,
                type_literal.members.iter().filter_map(|member| {
                    let TSSignature::TSPropertySignature(property) = member else {
                        return None;
                    };
                    let name = property_key_name_str(&property.key)?;
                    let ty =
                        Self::from_ts_type_annotation(arena, property.type_annotation.as_deref());
                    Some(Self::property(name, ty))
                }),
            ),
            TSType::TSArrayType(array) => {
                let element_type = Self::from_ts_type(arena, &array.element_type).to_type_string();
                let array_type = arena.concat_strs_array([element_type.as_str(), "[]"]);
                Self::type_(arena, array_type)
            }
            TSType::TSTypeReference(reference) => Self::from_ts_type_reference(arena, reference),
            TSType::TSParenthesizedType(parenthesized) => {
                Self::from_ts_type(arena, &parenthesized.type_annotation)
            }
            _ => Self::none(),
        }
    }

    fn from_ts_type_reference(arena: CheckerArena<'a>, reference: &TSTypeReference<'a>) -> Self {
        Self::type_reference(
            arena,
            ts_type_name_to_str(arena, &reference.type_name),
            reference
                .type_arguments
                .as_ref()
                .into_iter()
                .flat_map(|args| args.params.iter().map(|ty| Self::from_ts_type(arena, ty))),
        )
    }

    fn from_expression(expression: &Expression<'_>) -> Self {
        match expression {
            Expression::BooleanLiteral(_) => Self::boolean(),
            Expression::NumericLiteral(_) => Self::number(),
            Expression::BigIntLiteral(_) => Self::bigint(),
            Expression::StringLiteral(_) => Self::string(),
            Expression::NullLiteral(_) => Self::any(),
            _ => Self::any(),
        }
    }

    fn property_type(&self, name: &str) -> Option<Self> {
        match self {
            Self::Object(object) => object
                .properties
                .iter()
                .find_map(|property| (property.name == name).then_some(property.ty)),
            _ => None,
        }
    }

    fn substitute_type_parameters(
        &self,
        arena: CheckerArena<'a>,
        substitutions: &HashMap<&'a str, Ty<'a>>,
    ) -> Self {
        match self {
            Self::Object(object) => Self::object(
                arena,
                object.properties.iter().map(|property| {
                    Self::property(
                        property.name,
                        property.ty.substitute_type_parameters(arena, substitutions),
                    )
                }),
            ),
            Self::Function(function) => {
                let substitutions = substitutions
                    .iter()
                    .filter(|(name, _)| !function.type_parameters.contains(name))
                    .map(|(name, ty)| (*name, *ty))
                    .collect::<HashMap<_, _>>();
                Self::function(
                    arena,
                    function.type_parameters.iter().copied(),
                    function.parameters.iter().map(|parameter| {
                        Self::parameter(
                            parameter.name,
                            parameter
                                .ty
                                .substitute_type_parameters(arena, &substitutions),
                        )
                    }),
                    function
                        .return_type
                        .substitute_type_parameters(arena, &substitutions),
                )
            }
            Self::Type(ty) => substitutions.get(ty.name).copied().unwrap_or(*self),
            Self::TypeReference(reference) => {
                if reference.type_arguments.is_empty()
                    && let Some(substitution) = substitutions.get(reference.name)
                {
                    *substitution
                } else {
                    Self::type_reference(
                        arena,
                        reference.name,
                        reference
                            .type_arguments
                            .iter()
                            .map(|ty| ty.substitute_type_parameters(arena, substitutions)),
                    )
                }
            }
            _ => *self,
        }
    }

    fn to_type_string(self) -> String {
        match self {
            Self::None => "none".to_string(),
            Self::Number => "number".to_string(),
            Self::String => "string".to_string(),
            Self::Boolean => "boolean".to_string(),
            Self::Bigint => "bigint".to_string(),
            Self::Undefined => "undefined".to_string(),
            Self::Null => "null".to_string(),
            Self::Any => "any".to_string(),
            Self::Unknown => "unknown".to_string(),
            Self::Object(object) => {
                if object.properties.is_empty() {
                    return "{}".to_string();
                }

                let properties = object
                    .properties
                    .iter()
                    .map(|property| format!("{}: {};", property.name, property.ty.to_type_string()))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("{{ {properties} }}")
            }
            Self::Function(function) => {
                let type_parameters = if function.type_parameters.is_empty() {
                    String::new()
                } else {
                    format!("<{}>", function.type_parameters.join(", "))
                };
                let parameters = function
                    .parameters
                    .iter()
                    .map(|parameter| {
                        format!("{}: {}", parameter.name, parameter.ty.to_type_string())
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "{type_parameters}({parameters}) => {}",
                    function.return_type.to_type_string()
                )
            }
            Self::TypeReference(reference) => {
                if reference.type_arguments.is_empty() {
                    reference.name.to_string()
                } else {
                    let type_arguments = reference
                        .type_arguments
                        .iter()
                        .map(|ty| ty.to_type_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{type_arguments}>", reference.name)
                }
            }
            Self::Type(ty) => ty.name.to_string(),
        }
    }
}

fn infer_type_parameter_from_types<'a>(
    parameter_type: &Ty<'a>,
    argument_type: &Ty<'a>,
    type_parameters: &[&'a str],
    substitutions: &mut HashMap<&'a str, Ty<'a>>,
) {
    match (parameter_type, argument_type) {
        (Ty::Type(ty), _) if type_parameters.contains(&ty.name) => {
            match substitutions.get(ty.name) {
                Some(existing) if existing != argument_type => {
                    substitutions.insert(ty.name, Ty::any());
                }
                Some(_) => {}
                None => {
                    substitutions.insert(ty.name, *argument_type);
                }
            }
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

enum SignatureKind {
    Call,
    Construct,
}
struct Signature {}
struct IndexInfo {}

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
        match expression {
            Expression::Identifier(identifier) => identifier
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
                }),
            Expression::ObjectExpression(object) => {
                self.get_type_of_object_expression(program_id, object)
            }
            Expression::NewExpression(new_expression) => {
                self.get_type_of_new_expression(program_id, new_expression)
            }
            Expression::CallExpression(call_expression) => {
                self.get_type_of_call_expression(program_id, call_expression)
            }
            Expression::StaticMemberExpression(member) => {
                self.get_type_of_static_member_expression(program_id, member)
            }
            _ => Ty::from_expression(expression),
        }
    }

    fn get_type_of_object_expression(
        &self,
        program_id: program::ProgramId,
        object: &ObjectExpression<'a>,
    ) -> Ty<'a> {
        Ty::object(
            self.arena(),
            object.properties.iter().filter_map(|property| {
                let ObjectPropertyKind::ObjectProperty(property) = property else {
                    return None;
                };
                let name = property_key_name_str(&property.key)?;
                let ty = self.get_type_of_expression(program_id, &property.value);
                Some(Ty::property(name, ty))
            }),
        )
    }

    fn get_type_of_static_member_expression(
        &self,
        program_id: program::ProgramId,
        member: &StaticMemberExpression<'a>,
    ) -> Ty<'a> {
        let object_type = self.get_type_of_expression(program_id, &member.object);
        object_type
            .property_type(member.property.name.as_str())
            .or_else(|| {
                self.get_property_type_of_named_type(
                    program_id,
                    &object_type,
                    member.property.name.as_str(),
                )
            })
            .unwrap_or_else(Ty::any)
    }

    fn get_type_of_call_expression(
        &self,
        program_id: program::ProgramId,
        call_expression: &CallExpression<'a>,
    ) -> Ty<'a> {
        match self.get_type_of_expression(program_id, &call_expression.callee) {
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
                    let argument_type = self.get_type_of_expression(program_id, argument);
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

        if let Some(Ty::Type(ty)) = constructor_type
            && let Some(instance_name) = ty.name.strip_prefix("typeof ")
        {
            return Ty::type_(self.arena(), self.arena().str(instance_name));
        }

        Ty::type_(self.arena(), identifier.name.as_str())
    }

    fn get_property_type_of_named_type(
        &self,
        program_id: program::ProgramId,
        object_type: &Ty<'a>,
        property_name: &str,
    ) -> Option<Ty<'a>> {
        let type_name = match object_type {
            Ty::Type(ty) => ty.name,
            Ty::TypeReference(reference) => reference.name,
            _ => return None,
        };
        let is_static = type_name.starts_with("typeof ");
        let class_name = type_name.strip_prefix("typeof ").unwrap_or(type_name);
        let class_symbol = self.get_class_symbol_for_type(program_id, class_name)?;
        let class = self.get_class_for_symbol(class_symbol)?;
        self.get_class_member_type(class_symbol.program_id, class, property_name, is_static)
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

    fn get_class_for_symbol(&self, symbol: SymbolRef) -> Option<&'a Class<'a>> {
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        match self.nodes(symbol.program_id).kind(declaration) {
            AstKind::Class(class) => Some(class),
            AstKind::BindingIdentifier(_) => {
                if let AstKind::Class(class) =
                    self.nodes(symbol.program_id).parent_kind(declaration)
                {
                    Some(class)
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
        class: &'a Class<'a>,
        property_name: &str,
        is_static: bool,
    ) -> Option<Ty<'a>> {
        class.body.body.iter().find_map(|element| match element {
            ClassElement::MethodDefinition(method)
                if method.r#static == is_static
                    && property_key_name(&method.key).as_deref() == Some(property_name) =>
            {
                Some(self.get_type_of_function_signature(program_id, &method.value))
            }
            ClassElement::PropertyDefinition(property)
                if property.r#static == is_static
                    && property_key_name(&property.key).as_deref() == Some(property_name) =>
            {
                property.type_annotation.as_deref().map_or_else(
                    || {
                        property
                            .value
                            .as_ref()
                            .map(|value| self.get_type_of_expression(program_id, value))
                    },
                    |annotation| Some(Ty::from_ts_type_annotation(self.arena(), Some(annotation))),
                )
            }
            _ => None,
        })
    }

    fn get_type_of_function_signature(
        &self,
        program_id: program::ProgramId,
        function: &Function<'a>,
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
            || self.infer_function_return_type(program_id, function),
            |annotation| Ty::from_ts_type_annotation(self.arena(), Some(annotation)),
        );

        Ty::function(self.arena(), type_parameters, parameters, return_type)
    }

    fn infer_function_return_type(
        &self,
        program_id: program::ProgramId,
        function: &Function<'a>,
    ) -> Ty<'a> {
        let Some(body) = &function.body else {
            return Ty::any();
        };
        body.statements
            .iter()
            .find_map(|statement| {
                let Statement::ReturnStatement(statement) = statement else {
                    return None;
                };
                statement
                    .argument
                    .as_ref()
                    .map(|argument| self.get_return_expression_type(program_id, argument))
            })
            .unwrap_or_else(Ty::undefined)
    }

    fn get_return_expression_type(
        &self,
        program_id: program::ProgramId,
        expression: &Expression<'a>,
    ) -> Ty<'a> {
        match expression {
            Expression::NewExpression(new_expression) => {
                self.get_type_of_new_expression(program_id, new_expression)
            }
            _ => self.get_type_of_expression(program_id, expression),
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
            AstKind::TSPropertySignature(property) => {
                Ty::from_ts_type_annotation(self.arena(), property.type_annotation.as_deref())
            }
            AstKind::ObjectProperty(property) => {
                self.get_type_of_expression(node.program_id, &property.value)
            }
            AstKind::StaticMemberExpression(member) => {
                self.get_type_of_static_member_expression(node.program_id, member)
            }
            AstKind::MethodDefinition(method) => {
                self.get_type_of_function_signature(node.program_id, &method.value)
            }
            AstKind::PropertyDefinition(property) => {
                property.type_annotation.as_deref().map_or_else(
                    || {
                        property.value.as_ref().map_or_else(Ty::any, |value| {
                            self.get_type_of_expression(node.program_id, value)
                        })
                    },
                    |annotation| Ty::from_ts_type_annotation(self.arena(), Some(annotation)),
                )
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
                Ty::from_ts_type_annotation(self.arena(), parameter.type_annotation.as_deref())
            }
            AstKind::FormalParameterRest(parameter) => {
                Ty::from_ts_type_annotation(self.arena(), parameter.type_annotation.as_deref())
            }
            AstKind::CatchParameter(parameter) => {
                Ty::from_ts_type_annotation(self.arena(), parameter.type_annotation.as_deref())
            }
            AstKind::PropertyDefinition(property) => {
                Ty::from_ts_type_annotation(self.arena(), property.type_annotation.as_deref())
            }
            AstKind::Function(function) => {
                self.get_type_of_function_signature(sym.program_id, function)
            }
            AstKind::AccessorProperty(property) => {
                Ty::from_ts_type_annotation(self.arena(), property.type_annotation.as_deref())
            }
            AstKind::BindingIdentifier(identifier) => {
                match self.nodes(sym.program_id).parent_kind(declaration) {
                    AstKind::Class(_) => {
                        let name = self
                            .arena()
                            .concat_strs_array(["typeof ", identifier.name.as_str()]);
                        Ty::type_(self.arena(), name)
                    }
                    AstKind::Function(function) => {
                        self.get_type_of_function_signature(sym.program_id, function)
                    }
                    _ => Ty::none(),
                }
            }
            AstKind::Class(class) => class.id.as_ref().map_or_else(Ty::any, |identifier| {
                let name = self
                    .arena()
                    .concat_strs_array(["typeof ", identifier.name.as_str()]);
                Ty::type_(self.arena(), name)
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
                            self.get_type_of_expression(sym.program_id, expression)
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

    fn is_assignable_to(&self, _source: Ty<'a>, _target: Ty<'a>) -> bool {
        false
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
            Ty::type_(arena(&ret), "Foo")
        );
        assert_eq!(
            get_global_symbol_type(&ret, "x"),
            Ty::object(arena(&ret), [Ty::property("b", Ty::number())])
        );
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
}
