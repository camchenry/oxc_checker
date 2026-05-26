use oxc_allocator::{Allocator, Vec as ArenaVec};
use oxc_ast::ast::{
    BindingPattern, Expression, FormalParameter, FormalParameterRest, PropertyKey, TSLiteral,
    TSSignature, TSType, TSTypeAnnotation, TSTypeName, TSTypeReference,
};
use std::collections::HashMap;

#[derive(Clone, Copy)]
pub(crate) struct CheckerArena<'a> {
    allocator: &'a Allocator,
}

impl<'a> CheckerArena<'a> {
    pub(crate) fn new(allocator: &'a Allocator) -> Self {
        Self { allocator }
    }

    pub(crate) fn alloc<T>(&self, value: T) -> &'a T {
        self.allocator.alloc(value)
    }

    pub(crate) fn str(&self, value: &str) -> &'a str {
        self.allocator.alloc_str(value)
    }

    pub(crate) fn concat_strs_array<const N: usize>(&self, strings: [&str; N]) -> &'a str {
        self.allocator.alloc_concat_strs_array(strings)
    }

    pub(crate) fn vec_from_iter<T>(&self, iter: impl IntoIterator<Item = T>) -> ArenaVec<'a, T> {
        ArenaVec::from_iter_in(iter, self.allocator)
    }
}

#[repr(C, u8)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum Ty<'a> {
    None,
    Number,
    String,
    Boolean,
    Bigint,
    Undefined,
    Null,
    Any,
    Unknown,
    Void,
    Object(&'a TyObject<'a>),
    Function(&'a TyFunction<'a>),
    TypeReference(&'a TyTypeReference<'a>),
    Literal(&'a TyLiteral<'a>),
    Array(&'a TyArray<'a>),
    Union(&'a TyUnion<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyObject<'a> {
    pub(crate) properties: ArenaVec<'a, TyProperty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyProperty<'a> {
    pub(crate) name: &'a str,
    pub(crate) ty: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyFunction<'a> {
    pub(crate) type_parameters: ArenaVec<'a, &'a str>,
    pub(crate) parameters: ArenaVec<'a, TyParameter<'a>>,
    pub(crate) return_type: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyParameter<'a> {
    pub(crate) name: &'a str,
    pub(crate) ty: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyTypeReference<'a> {
    pub(crate) name: &'a str,
    pub(crate) type_arguments: ArenaVec<'a, Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyLiteral<'a> {
    pub(crate) name: &'a str,
    pub(crate) primitive: TyLiteralPrimitiveType,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum TyLiteralPrimitiveType {
    Number,
    String,
    Boolean,
    BigInt,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyArray<'a> {
    pub(crate) element_type: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyUnion<'a> {
    pub(crate) types: ArenaVec<'a, Ty<'a>>,
    // TODO: Add flags
}

impl<'a> Ty<'a> {
    pub(crate) fn none() -> Self {
        Self::None
    }

    pub(crate) fn number() -> Self {
        Self::Number
    }

    pub(crate) fn number_literal(arena: CheckerArena<'a>, num: &'a str) -> Self {
        Self::literal(arena, TyLiteralPrimitiveType::Number, num)
    }

    pub(crate) fn string() -> Self {
        Self::String
    }

    /// General `boolean` type (true or false)
    pub(crate) fn boolean() -> Self {
        Self::Boolean
    }

    /// Literal `boolean` type (`true` or `false`), subtype of `boolean`
    pub(crate) fn boolean_literal(arena: CheckerArena<'a>, value: bool) -> Self {
        if value {
            Self::boolean_true(arena)
        } else {
            Self::boolean_false(arena)
        }
    }

    /// Literal `true` type (subtype of `boolean`)
    pub(crate) fn boolean_true(arena: CheckerArena<'a>) -> Self {
        Self::literal(arena, TyLiteralPrimitiveType::Boolean, "true")
    }

    /// Literal `false` type (subtype of `boolean`)
    pub(crate) fn boolean_false(arena: CheckerArena<'a>) -> Self {
        Self::literal(arena, TyLiteralPrimitiveType::Boolean, "false")
    }

    pub(crate) fn bigint() -> Self {
        Self::Bigint
    }

    pub(crate) fn bigint_literal(arena: CheckerArena<'a>, name: &'a str) -> Self {
        Self::literal(arena, TyLiteralPrimitiveType::BigInt, name)
    }

    pub(crate) fn undefined() -> Self {
        Self::Undefined
    }

    pub(crate) fn null() -> Self {
        Self::Null
    }

    pub(crate) fn any() -> Self {
        Self::Any
    }

    pub(crate) fn unknown() -> Self {
        Self::Unknown
    }

    pub(crate) fn void() -> Self {
        Self::Void
    }

    pub(crate) fn property(name: &'a str, ty: Ty<'a>) -> TyProperty<'a> {
        TyProperty { name, ty }
    }

    pub(crate) fn parameter(name: &'a str, ty: Ty<'a>) -> TyParameter<'a> {
        TyParameter { name, ty }
    }

    pub(crate) fn object(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
    ) -> Self {
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(properties),
        }))
    }

    pub(crate) fn function(
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

    pub(crate) fn type_reference(
        arena: CheckerArena<'a>,
        name: &'a str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        Self::TypeReference(arena.alloc(TyTypeReference {
            name,
            type_arguments: arena.vec_from_iter(type_arguments),
        }))
    }

    pub(crate) fn literal(
        arena: CheckerArena<'a>,
        primitive: TyLiteralPrimitiveType,
        name: &'a str,
    ) -> Self {
        Self::Literal(arena.alloc(TyLiteral { name, primitive }))
    }

    pub(crate) fn string_literal(arena: CheckerArena<'a>, name: &'a str) -> Self {
        Self::literal(arena, TyLiteralPrimitiveType::String, name)
    }

    pub(crate) fn array(arena: CheckerArena<'a>, element_type: Ty<'a>) -> Self {
        Self::Array(arena.alloc(TyArray { element_type }))
    }

    pub(crate) fn r#union(
        arena: CheckerArena<'a>,
        types: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        Self::Union(arena.alloc(TyUnion {
            types: arena.vec_from_iter(types),
        }))
    }

    pub(crate) fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }

    pub(crate) fn enum_variant_name(self) -> &'static str {
        match self {
            Self::None => "TyNone",
            Self::Number => "TyNumber",
            Self::String => "TyString",
            Self::Boolean => "TyBoolean",
            Self::Bigint => "TyBigint",
            Self::Undefined => "TyUndefined",
            Self::Null => "TyNull",
            Self::Any => "TyAny",
            Self::Unknown => "TyUnknown",
            Self::Void => "TyVoid",
            Self::Object(_) => "TyObject",
            Self::Function(_) => "TyFunction",
            Self::TypeReference(_) => "TyTypeReference",
            Self::Literal(_) => "TyLiteral",
            Self::Array(_) => "TyArray",
            Self::Union(_) => "TyUnion",
        }
    }

    /// Take a type annotation like `: number` and return the corresponding type. Returns no
    /// type if there is no type annotation.
    pub(crate) fn from_ts_type_annotation(
        arena: CheckerArena<'a>,
        type_annotation: Option<&TSTypeAnnotation<'a>>,
    ) -> Self {
        type_annotation.map_or_else(Self::any, |type_annotation| {
            Self::from_ts_type(arena, &type_annotation.type_annotation)
        })
    }

    /// Turns a declared type in the AST and turns it into an actual type.
    pub(crate) fn from_ts_type(arena: CheckerArena<'a>, t: &TSType<'a>) -> Self {
        match t {
            TSType::TSNumberKeyword(_) => Self::number(),
            TSType::TSStringKeyword(_) => Self::string(),
            TSType::TSBooleanKeyword(_) => Self::boolean(),
            TSType::TSBigIntKeyword(_) => Self::bigint(),
            TSType::TSUndefinedKeyword(_) => Self::undefined(),
            TSType::TSNullKeyword(_) => Self::null(),
            TSType::TSAnyKeyword(_) => Self::any(),
            TSType::TSUnknownKeyword(_) => Self::unknown(),
            TSType::TSVoidKeyword(_) => Self::void(),
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
                Self::array(arena, Self::from_ts_type(arena, &array.element_type))
            }
            TSType::TSTypeReference(reference) => Self::from_ts_type_reference(arena, reference),
            TSType::TSParenthesizedType(parenthesized) => {
                Self::from_ts_type(arena, &parenthesized.type_annotation)
            }
            TSType::TSUnionType(r#union) => Self::r#union(
                arena,
                r#union.types.iter().map(|ty| Self::from_ts_type(arena, ty)),
            ),
            TSType::TSFunctionType(function) => Self::function(
                arena,
                function
                    .type_parameters
                    .as_ref()
                    .map_or_else(Vec::new, |params| {
                        params
                            .params
                            .iter()
                            .map(|parameter| parameter.name.name.as_str())
                            .collect()
                    }),
                function_type_parameters(arena, function.params.as_ref()),
                Self::from_ts_type_annotation(arena, Some(&function.return_type)),
            ),
            TSType::TSLiteralType(literal) => match &literal.literal {
                TSLiteral::BooleanLiteral(boolean_literal) => {
                    if boolean_literal.value {
                        Self::boolean_true(arena)
                    } else {
                        Self::boolean_false(arena)
                    }
                }
                TSLiteral::NumericLiteral(numeric_literal) => {
                    let name = numeric_literal.raw.as_ref().map_or_else(
                        || arena.str(&numeric_literal.value.to_string()),
                        |raw| raw.as_str(),
                    );
                    Self::number_literal(arena, name)
                }
                TSLiteral::StringLiteral(string_literal) => {
                    Self::string_literal(arena, string_literal.value.as_str())
                }
                TSLiteral::BigIntLiteral(bigint_literal) => {
                    Self::bigint_literal(arena, bigint_literal.value.as_str())
                }
                TSLiteral::TemplateLiteral(_) => Ty::none(),
                TSLiteral::UnaryExpression(_) => Ty::none(),
            },
            _ => Self::none(),
        }
    }

    pub(crate) fn from_ts_type_reference(
        arena: CheckerArena<'a>,
        reference: &TSTypeReference<'a>,
    ) -> Self {
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

    pub(crate) fn from_expression(expression: &Expression<'_>) -> Self {
        match expression {
            Expression::BooleanLiteral(_) => Self::boolean(),
            Expression::NumericLiteral(_) => Self::number(),
            Expression::BigIntLiteral(_) => Self::bigint(),
            Expression::StringLiteral(_) => Self::string(),
            Expression::NullLiteral(_) => Self::any(),
            _ => Self::any(),
        }
    }

    pub(crate) fn property_type(&self, name: &str) -> Option<Self> {
        match self {
            Self::Object(object) => object
                .properties
                .iter()
                .find_map(|property| (property.name == name).then_some(property.ty)),
            _ => None,
        }
    }

    pub(crate) fn substitute_type_parameters(
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
            Self::Array(array) => Self::array(
                arena,
                array
                    .element_type
                    .substitute_type_parameters(arena, substitutions),
            ),
            _ => *self,
        }
    }

    pub(crate) fn to_type_string(self) -> String {
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
            Self::Void => "void".to_string(),
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
            Self::Literal(literal) => literal_to_type_string(literal),
            Self::Array(array) => {
                let element_type = array.element_type.to_type_string();
                if array.element_type.display_needs_parentheses() {
                    format!("({element_type})[]")
                } else {
                    format!("{element_type}[]")
                }
            }
            Self::Union(union) => union
                .types
                .iter()
                .map(|ty| ty.to_type_string())
                .collect::<Vec<_>>()
                .join(" | "),
        }
    }

    /// Whether this type needs parentheses when printed
    fn display_needs_parentheses(&self) -> bool {
        matches!(self, Self::Function(_) | Self::Union(_))
    }
}

pub(crate) enum SignatureKind {
    Call,
    Construct,
}

pub(crate) struct Signature {}

pub(crate) struct IndexInfo {}

fn property_key_name_str<'a>(key: &PropertyKey<'a>) -> Option<&'a str> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.name.as_str()),
        _ => None,
    }
}

fn binding_pattern_name_str<'a>(pattern: &BindingPattern<'a>) -> Option<&'a str> {
    match pattern {
        BindingPattern::BindingIdentifier(identifier) => Some(identifier.name.as_str()),
        _ => None,
    }
}

fn function_type_parameters<'a>(
    arena: CheckerArena<'a>,
    params: &oxc_ast::ast::FormalParameters<'a>,
) -> Vec<TyParameter<'a>> {
    params
        .items
        .iter()
        .map(|parameter| function_type_parameter(arena, parameter))
        .chain(
            params
                .rest
                .iter()
                .map(|parameter| function_type_rest_parameter(arena, parameter)),
        )
        .collect()
}

fn function_type_parameter<'a>(
    arena: CheckerArena<'a>,
    parameter: &FormalParameter<'a>,
) -> TyParameter<'a> {
    let name = binding_pattern_name_str(&parameter.pattern).unwrap_or("_");
    let name = if parameter.optional {
        arena.concat_strs_array([name, "?"])
    } else {
        name
    };
    Ty::parameter(
        name,
        Ty::from_ts_type_annotation(arena, parameter.type_annotation.as_deref()),
    )
}

fn function_type_rest_parameter<'a>(
    arena: CheckerArena<'a>,
    parameter: &FormalParameterRest<'a>,
) -> TyParameter<'a> {
    let name = binding_pattern_name_str(&parameter.rest.argument).unwrap_or("_");
    Ty::parameter(
        arena.concat_strs_array(["...", name]),
        Ty::from_ts_type_annotation(arena, parameter.type_annotation.as_deref()),
    )
}

fn literal_to_type_string(literal: &TyLiteral<'_>) -> String {
    match literal.primitive {
        TyLiteralPrimitiveType::String => string_literal_to_type_string(literal.name),
        TyLiteralPrimitiveType::Number | TyLiteralPrimitiveType::Boolean => {
            literal.name.to_string()
        }
        TyLiteralPrimitiveType::BigInt => format!("{}n", literal.name),
    }
}

fn string_literal_to_type_string(name: &str) -> String {
    let content = name
        .strip_prefix('\'')
        .and_then(|name| name.strip_suffix('\''))
        .or_else(|| {
            name.strip_prefix('"')
                .and_then(|name| name.strip_suffix('"'))
        })
        .unwrap_or(name);
    format!("{content:?}")
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
