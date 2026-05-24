#![allow(dead_code, unused_imports)]
use oxc_ast::{
    AstKind,
    ast::{
        BindingPattern, CallExpression, Class, ClassElement, Expression, Function, NewExpression,
        ObjectExpression, ObjectPropertyKind, Program, PropertyKey, Statement,
        StaticMemberExpression, TSSignature, TSType, TSTypeAnnotation, TSTypeName,
        VariableDeclarator,
    },
};
use oxc_index::nonmax::NonMaxU32;
use oxc_semantic::{AstNode, AstNodes, NodeId, Semantic, SemanticBuilder, SymbolId};
use oxc_span::{GetSpan, Span};
use oxc_str::Ident;
use std::{cell::RefCell, collections::HashMap};

pub mod program;

// TODO: Make use of the same pattern in oxc_ast for ast node types
#[derive(Debug, PartialEq, Eq, Clone)]
enum Ty {
    None,
    Number,
    String,
    Boolean,
    Bigint,
    Undefined,
    Null,
    Any,
    Unknown,
    Object(Vec<(String, Ty)>),
    Function {
        type_parameters: Vec<String>,
        parameters: Vec<(String, Ty)>,
        return_type: Box<Ty>,
    },
    Type(String),
}

impl Ty {
    /// Take a type annotation like `: number` and return the corresponding type. Returns no
    /// type if there is no type annotation.
    fn from_ts_type_annotation(type_annotation: Option<&TSTypeAnnotation<'_>>) -> Self {
        type_annotation.map_or(Self::Any, |type_annotation| {
            Self::from_ts_type(&type_annotation.type_annotation)
        })
    }

    /// Turns a declared type in the AST and turns it into an actual type.
    fn from_ts_type(t: &TSType<'_>) -> Self {
        match t {
            TSType::TSNumberKeyword(_) => Self::Number,
            TSType::TSStringKeyword(_) => Self::String,
            TSType::TSBooleanKeyword(_) => Self::Boolean,
            TSType::TSBigIntKeyword(_) => Self::Bigint,
            TSType::TSUndefinedKeyword(_) => Self::Undefined,
            TSType::TSNullKeyword(_) => Self::Null,
            TSType::TSAnyKeyword(_) => Self::Any,
            TSType::TSUnknownKeyword(_) => Self::Unknown,
            TSType::TSTypeLiteral(type_literal) => Self::Object(
                type_literal
                    .members
                    .iter()
                    .filter_map(|member| {
                        let TSSignature::TSPropertySignature(property) = member else {
                            return None;
                        };
                        let name = property_key_name(&property.key)?;
                        let ty = Self::from_ts_type_annotation(property.type_annotation.as_deref());
                        Some((name.to_string(), ty))
                    })
                    .collect(),
            ),
            TSType::TSArrayType(array) => Self::Type(format!(
                "{}[]",
                Self::from_ts_type(&array.element_type).to_type_string()
            )),
            TSType::TSTypeReference(reference) => {
                Self::Type(ts_type_name_to_string(&reference.type_name))
            }
            TSType::TSParenthesizedType(parenthesized) => {
                Self::from_ts_type(&parenthesized.type_annotation)
            }
            _ => Self::None,
        }
    }

    fn from_expression(expression: &Expression<'_>) -> Self {
        match expression {
            Expression::BooleanLiteral(_) => Self::Boolean,
            Expression::NumericLiteral(_) => Self::Number,
            Expression::BigIntLiteral(_) => Self::Bigint,
            Expression::StringLiteral(_) => Self::String,
            Expression::NullLiteral(_) => Self::Any,
            _ => Self::Any,
        }
    }

    fn property_type(&self, name: &str) -> Option<Self> {
        match self {
            Self::Object(properties) => properties
                .iter()
                .find_map(|(property_name, ty)| (property_name == name).then(|| ty.clone())),
            _ => None,
        }
    }

    fn substitute_type_parameters(&self, substitutions: &HashMap<String, Ty>) -> Self {
        match self {
            Self::Object(properties) => Self::Object(
                properties
                    .iter()
                    .map(|(name, ty)| (name.clone(), ty.substitute_type_parameters(substitutions)))
                    .collect(),
            ),
            Self::Function {
                type_parameters,
                parameters,
                return_type,
            } => {
                let substitutions = substitutions
                    .iter()
                    .filter(|(name, _)| !type_parameters.contains(name))
                    .map(|(name, ty)| (name.clone(), ty.clone()))
                    .collect::<HashMap<_, _>>();
                Self::Function {
                    type_parameters: type_parameters.clone(),
                    parameters: parameters
                        .iter()
                        .map(|(name, ty)| {
                            (name.clone(), ty.substitute_type_parameters(&substitutions))
                        })
                        .collect(),
                    return_type: Box::new(return_type.substitute_type_parameters(&substitutions)),
                }
            }
            Self::Type(name) => substitutions
                .get(name)
                .cloned()
                .unwrap_or_else(|| self.clone()),
            _ => self.clone(),
        }
    }

    fn to_type_string(&self) -> String {
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
            Self::Object(properties) => {
                if properties.is_empty() {
                    return "{}".to_string();
                }

                let properties = properties
                    .iter()
                    .map(|(name, ty)| format!("{name}: {};", ty.to_type_string()))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("{{ {properties} }}")
            }
            Self::Function {
                type_parameters,
                parameters,
                return_type,
            } => {
                let type_parameters = if type_parameters.is_empty() {
                    String::new()
                } else {
                    format!("<{}>", type_parameters.join(", "))
                };
                let parameters = parameters
                    .iter()
                    .map(|(name, ty)| format!("{name}: {}", ty.to_type_string()))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "{type_parameters}({parameters}) => {}",
                    return_type.to_type_string()
                )
            }
            Self::Type(ty) => ty.clone(),
        }
    }
}

fn infer_type_parameter_from_types(
    parameter_type: &Ty,
    argument_type: &Ty,
    type_parameters: &[String],
    substitutions: &mut HashMap<String, Ty>,
) {
    match (parameter_type, argument_type) {
        (Ty::Type(name), _) if type_parameters.contains(name) => match substitutions.get(name) {
            Some(existing) if existing != argument_type => {
                substitutions.insert(name.clone(), Ty::Any);
            }
            Some(_) => {}
            None => {
                substitutions.insert(name.clone(), argument_type.clone());
            }
        },
        (Ty::Object(parameter_properties), Ty::Object(argument_properties)) => {
            for (property_name, parameter_property_type) in parameter_properties {
                if let Some((_, argument_property_type)) = argument_properties
                    .iter()
                    .find(|(argument_property_name, _)| argument_property_name == property_name)
                {
                    infer_type_parameter_from_types(
                        parameter_property_type,
                        argument_property_type,
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

fn binding_pattern_name(pattern: &BindingPattern<'_>) -> Option<String> {
    match pattern {
        BindingPattern::BindingIdentifier(identifier) => Some(identifier.name.to_string()),
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

trait Checker {
    fn get_symbol_at_location(&self, node: NodeRef) -> Option<SymbolRef>;
    fn get_type_at_location(&self, node: NodeRef) -> Ty;
    // fn get_type_from_type_node(&self, type_node: NodeRef) -> Ty;
    fn get_declared_type_of_symbol(&self, sym: SymbolRef) -> Ty;
    fn get_type_of_symbol(&self, sym: SymbolRef) -> Ty;
    fn get_type_of_symbol_at_location(&self, node: NodeRef) -> Ty;
    fn get_properties_of_type(&self, t: Ty) -> Vec<SymbolRef>;
    fn get_property_of_type(&self, t: Ty, name: &str) -> Option<SymbolRef>;
    fn get_signatures_of_type(&self, t: Ty, kind: SignatureKind) -> Vec<Signature>;
    fn get_index_infos_of_type(&self, t: Ty) -> Vec<IndexInfo>;
    fn is_assignable_to(&self, source: Ty, target: Ty) -> bool;
    fn type_to_string(&self, t: Ty, location: NodeRef) -> String;
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

    fn get_type_of_expression(
        &self,
        program_id: program::ProgramId,
        expression: &Expression<'_>,
    ) -> Ty {
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
                .map_or(Ty::Any, |symbol_id| {
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
        object: &ObjectExpression<'_>,
    ) -> Ty {
        Ty::Object(
            object
                .properties
                .iter()
                .filter_map(|property| {
                    let ObjectPropertyKind::ObjectProperty(property) = property else {
                        return None;
                    };
                    let name = property_key_name(&property.key)?;
                    let ty = self.get_type_of_expression(program_id, &property.value);
                    Some((name, ty))
                })
                .collect(),
        )
    }

    fn get_type_of_static_member_expression(
        &self,
        program_id: program::ProgramId,
        member: &StaticMemberExpression<'_>,
    ) -> Ty {
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
            .unwrap_or(Ty::Any)
    }

    fn get_type_of_call_expression(
        &self,
        program_id: program::ProgramId,
        call_expression: &CallExpression<'_>,
    ) -> Ty {
        match self.get_type_of_expression(program_id, &call_expression.callee) {
            Ty::Function {
                type_parameters,
                parameters,
                return_type,
            } => {
                if type_parameters.is_empty() {
                    return *return_type;
                }

                let mut substitutions = HashMap::new();
                let mut explicit_type_parameters = Vec::new();

                if let Some(type_arguments) = &call_expression.type_arguments {
                    for (type_parameter, type_argument) in
                        type_parameters.iter().zip(type_arguments.params.iter())
                    {
                        substitutions
                            .insert(type_parameter.clone(), Ty::from_ts_type(type_argument));
                        explicit_type_parameters.push(type_parameter.clone());
                    }
                }

                let inferable_type_parameters = type_parameters
                    .iter()
                    .filter(|type_parameter| !explicit_type_parameters.contains(type_parameter))
                    .cloned()
                    .collect::<Vec<_>>();

                for (argument, (_, parameter_type)) in
                    call_expression.arguments.iter().zip(parameters.iter())
                {
                    let Some(argument) = argument.as_expression() else {
                        continue;
                    };
                    let argument_type = self.get_type_of_expression(program_id, argument);
                    infer_type_parameter_from_types(
                        parameter_type,
                        &argument_type,
                        &inferable_type_parameters,
                        &mut substitutions,
                    );
                }

                return_type.substitute_type_parameters(&substitutions)
            }
            _ => Ty::Any,
        }
    }

    fn get_type_of_new_expression(
        &self,
        program_id: program::ProgramId,
        new_expression: &NewExpression<'_>,
    ) -> Ty {
        let Expression::Identifier(identifier) = &new_expression.callee else {
            return Ty::Any;
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

        if let Some(Ty::Type(type_name)) = constructor_type
            && let Some(instance_name) = type_name.strip_prefix("typeof ")
        {
            return Ty::Type(instance_name.to_string());
        }

        Ty::Type(identifier.name.to_string())
    }

    fn get_property_type_of_named_type(
        &self,
        program_id: program::ProgramId,
        object_type: &Ty,
        property_name: &str,
    ) -> Option<Ty> {
        let Ty::Type(type_name) = object_type else {
            return None;
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

    fn get_class_for_symbol(&self, symbol: SymbolRef) -> Option<&Class<'_>> {
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
        class: &Class<'_>,
        property_name: &str,
        is_static: bool,
    ) -> Option<Ty> {
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
                    |annotation| Some(Ty::from_ts_type_annotation(Some(annotation))),
                )
            }
            _ => None,
        })
    }

    fn get_type_of_function_signature(
        &self,
        program_id: program::ProgramId,
        function: &Function<'_>,
    ) -> Ty {
        let type_parameters = function
            .type_parameters
            .as_ref()
            .map_or_else(Vec::new, |params| {
                params
                    .params
                    .iter()
                    .map(|parameter| parameter.name.to_string())
                    .collect()
            });
        let parameters = function
            .params
            .items
            .iter()
            .map(|parameter| {
                let name =
                    binding_pattern_name(&parameter.pattern).unwrap_or_else(|| "_".to_string());
                let ty = Ty::from_ts_type_annotation(parameter.type_annotation.as_deref());
                (name, ty)
            })
            .collect::<Vec<_>>();
        let return_type = function.return_type.as_deref().map_or_else(
            || self.infer_function_return_type(program_id, function),
            |annotation| Ty::from_ts_type_annotation(Some(annotation)),
        );

        Ty::Function {
            type_parameters,
            parameters,
            return_type: Box::new(return_type),
        }
    }

    fn infer_function_return_type(
        &self,
        program_id: program::ProgramId,
        function: &Function<'_>,
    ) -> Ty {
        let Some(body) = &function.body else {
            return Ty::Any;
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
            .unwrap_or(Ty::Undefined)
    }

    fn get_return_expression_type(
        &self,
        program_id: program::ProgramId,
        expression: &Expression<'_>,
    ) -> Ty {
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

    fn get_type_of_import_symbol(&self, symbol: SymbolRef) -> Option<Ty> {
        self.get_imported_symbol(symbol)
            .map(|imported_symbol| self.get_type_of_symbol(imported_symbol))
    }
}

impl Checker for CheckerReturn<'_, '_> {
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

    fn get_type_at_location(&self, node: NodeRef) -> Ty {
        match self.node_kind(node) {
            AstKind::TSPropertySignature(property) => {
                Ty::from_ts_type_annotation(property.type_annotation.as_deref())
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
                        property.value.as_ref().map_or(Ty::Any, |value| {
                            self.get_type_of_expression(node.program_id, value)
                        })
                    },
                    |annotation| Ty::from_ts_type_annotation(Some(annotation)),
                )
            }
            _ => self
                .get_symbol_at_location(node)
                .map_or(Ty::None, |sym| self.get_type_of_symbol(sym)),
        }
    }

    fn get_declared_type_of_symbol(&self, sym: SymbolRef) -> Ty {
        let declaration = self
            .semantic(sym.program_id)
            .scoping()
            .symbol_declaration(sym.symbol_id);
        match self.nodes(sym.program_id).kind(declaration) {
            AstKind::VariableDeclarator(declarator) => {
                Ty::from_ts_type_annotation(declarator.type_annotation.as_deref())
            }
            AstKind::FormalParameter(parameter) => {
                Ty::from_ts_type_annotation(parameter.type_annotation.as_deref())
            }
            AstKind::FormalParameterRest(parameter) => {
                Ty::from_ts_type_annotation(parameter.type_annotation.as_deref())
            }
            AstKind::CatchParameter(parameter) => {
                Ty::from_ts_type_annotation(parameter.type_annotation.as_deref())
            }
            AstKind::PropertyDefinition(property) => {
                Ty::from_ts_type_annotation(property.type_annotation.as_deref())
            }
            AstKind::Function(function) => {
                self.get_type_of_function_signature(sym.program_id, function)
            }
            AstKind::AccessorProperty(property) => {
                Ty::from_ts_type_annotation(property.type_annotation.as_deref())
            }
            AstKind::BindingIdentifier(identifier) => {
                match self.nodes(sym.program_id).parent_kind(declaration) {
                    AstKind::Class(_) => Ty::Type(format!("typeof {}", identifier.name)),
                    AstKind::Function(function) => {
                        self.get_type_of_function_signature(sym.program_id, function)
                    }
                    _ => Ty::None,
                }
            }
            AstKind::Class(class) => class.id.as_ref().map_or(Ty::Any, |identifier| {
                Ty::Type(format!("typeof {}", identifier.name))
            }),
            _ => Ty::None,
        }
    }

    fn get_type_of_symbol(&self, sym: SymbolRef) -> Ty {
        {
            let mut resolving_symbols = self.resolving_symbols.borrow_mut();
            if resolving_symbols.contains(&sym) {
                return Ty::Any;
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
                        Ty::from_ts_type_annotation(declarator.type_annotation.as_deref())
                    } else {
                        declarator.init.as_ref().map_or(Ty::Any, |expression| {
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

    fn get_type_of_symbol_at_location(&self, node: NodeRef) -> Ty {
        self.get_type_at_location(node)
    }

    fn get_properties_of_type(&self, _t: Ty) -> Vec<SymbolRef> {
        Vec::new()
    }

    fn get_property_of_type(&self, _t: Ty, _name: &str) -> Option<SymbolRef> {
        None
    }

    fn get_signatures_of_type(&self, _t: Ty, _kind: SignatureKind) -> Vec<Signature> {
        Vec::new()
    }

    fn get_index_infos_of_type(&self, _t: Ty) -> Vec<IndexInfo> {
        Vec::new()
    }

    fn is_assignable_to(&self, _source: Ty, _target: Ty) -> bool {
        false
    }

    fn type_to_string(&self, t: Ty, _location: NodeRef) -> String {
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

    fn get_global_symbol_type(ret: &ParseAndCheck, name: &str) -> Ty {
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

    fn get_symbol_type_in_function(ret: &ParseAndCheck, func_name: &str, param_name: &str) -> Ty {
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

        assert_eq!(get_global_symbol_type(&ret, "a"), Ty::Number);
        assert_eq!(get_global_symbol_type(&ret, "b"), Ty::String);
        assert_eq!(get_global_symbol_type(&ret, "c"), Ty::Boolean);
        assert_eq!(get_global_symbol_type(&ret, "d"), Ty::Bigint);
        assert_eq!(get_global_symbol_type(&ret, "e"), Ty::Undefined);
        assert_eq!(get_global_symbol_type(&ret, "f"), Ty::Null);
        assert_eq!(get_global_symbol_type(&ret, "g"), Ty::Any);
        assert_eq!(get_global_symbol_type(&ret, "h"), Ty::Unknown);
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

        assert_eq!(get_global_symbol_type(&ret, "l7"), Ty::Boolean);
        assert_eq!(get_global_symbol_type(&ret, "n"), Ty::Number);
        assert_eq!(get_global_symbol_type(&ret, "s"), Ty::String);
        assert_eq!(get_global_symbol_type(&ret, "b"), Ty::Bigint);
        assert_eq!(get_global_symbol_type(&ret, "a"), Ty::Any);
        assert_eq!(get_global_symbol_type(&ret, "annotated"), Ty::String);
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

        assert_eq!(get_global_symbol_type(&ret, "x"), Ty::Number);
        assert_eq!(get_global_symbol_type(&ret, "y"), Ty::String);
        assert_eq!(get_global_symbol_type(&ret, "z"), Ty::Boolean);
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

        assert_eq!(get_global_symbol_type(&ret, "x"), Ty::String);
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
            Ty::Object(vec![("value".to_string(), Ty::Number)])
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
            Ty::Type("Foo".to_string())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "x"),
            Ty::Object(vec![("b".to_string(), Ty::Number)])
        );
    }

    #[test]
    fn function_parameter_declared_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "function foo(a: number, b: string, c: boolean) {}",
        );

        assert_eq!(get_symbol_type_in_function(&ret, "foo", "a"), Ty::Number);
        assert_eq!(get_symbol_type_in_function(&ret, "foo", "b"), Ty::String);
        assert_eq!(get_symbol_type_in_function(&ret, "foo", "c"), Ty::Boolean);
    }
}
