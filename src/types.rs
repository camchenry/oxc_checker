use oxc_allocator::{Allocator, Vec as ArenaVec};
use oxc_ast::ast::{
    BindingPattern, Expression, FormalParameter, FormalParameterRest, PropertyKey, TSLiteral,
    TSSignature, TSTemplateLiteralType, TSThisParameter, TSTupleElement, TSType, TSTypeAnnotation,
    TSTypeName, TSTypeOperatorOperator, TSTypeParameter, TSTypeParameterDeclaration,
    TSTypeReference,
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
    Symbol,
    Undefined,
    Null,
    Any,
    Unknown,
    Void,
    Never,
    /// Primitive `object` keyword (not to be confused with `{}`)
    PrimitiveObject,
    Object(&'a TyObject<'a>),
    ModuleNamespace(&'a TyModuleNamespace<'a>),
    Function(&'a TyFunction<'a>),
    TypeReference(&'a TyTypeReference<'a>),
    StringLiteral(&'a TyStringLiteral<'a>),
    NumberLiteral(&'a TyNumberLiteral<'a>),
    BooleanLiteral(&'a TyBooleanLiteral),
    BigIntLiteral(&'a TyBigIntLiteral<'a>),
    TemplateLiteral(&'a TyTemplateLiteral<'a>),
    Array(&'a TyArray<'a>),
    Tuple(&'a TyTuple<'a>),
    Union(&'a TyUnion<'a>),
    Intersection(&'a TyIntersection<'a>),
    Keyof(&'a TyKeyof<'a>),
    IndexedAccess(&'a TyIndexedAccess<'a>),
    Conditional(&'a TyConditional<'a>),
    Infer(&'a TyInfer<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyObject<'a> {
    pub(crate) properties: ArenaVec<'a, TyProperty<'a>>,
    pub(crate) signatures: ArenaVec<'a, Signature<'a>>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyModuleNamespace<'a> {
    pub(crate) name: &'a str,
    pub(crate) properties: ArenaVec<'a, TyProperty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyProperty<'a> {
    pub(crate) name: &'a str,
    pub(crate) ty: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyFunction<'a> {
    pub(crate) type_parameters: ArenaVec<'a, TyTypeParameter<'a>>,
    pub(crate) parameters: ArenaVec<'a, TyParameter<'a>>,
    pub(crate) return_type: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyTypeParameter<'a> {
    pub(crate) name: &'a str,
    /// constraint type (e.g., `U` in `T extends U`)
    pub(crate) constraint_type: Option<Ty<'a>>,
    pub(crate) default_type: Option<Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyParameter<'a> {
    pub(crate) name: &'a str,
    pub(crate) ty: Ty<'a>,
    pub(crate) optional: bool,
    pub(crate) rest: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyTypeReference<'a> {
    pub(crate) name: &'a str,
    pub(crate) type_arguments: ArenaVec<'a, Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyStringLiteral<'a> {
    pub(crate) value: &'a str,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyNumberLiteral<'a> {
    // TODO(ast): use a number type?
    pub(crate) value: &'a str,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyBooleanLiteral {
    pub(crate) value: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TyBigIntLiteral<'a> {
    // TODO(ast): use a number type?
    pub(crate) value: &'a str,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyTemplateLiteral<'a> {
    pub(crate) quasis: ArenaVec<'a, TemplateLiteralElement<'a>>,
    pub(crate) expressions: ArenaVec<'a, Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TemplateLiteralElement<'a> {
    pub(crate) value: &'a str,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum TyLiteralPrimitiveType {
    Number,
    String,
    Boolean,
    BigInt,
    Template,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyArray<'a> {
    pub(crate) element_type: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyTuple<'a> {
    pub(crate) elements: ArenaVec<'a, TupleElement<'a>>,
}

/// A tuple element is either: a regular type [`Ty`], a rest type, or an optional type.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum TupleElement<'a> {
    Regular(Ty<'a>),
    Rest(Ty<'a>),
    Optional(Ty<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyUnion<'a> {
    pub(crate) types: ArenaVec<'a, Ty<'a>>,
    // TODO: Add flags
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyIntersection<'a> {
    pub(crate) types: ArenaVec<'a, Ty<'a>>,
    // TODO: Add flags
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyKeyof<'a> {
    pub(crate) target: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyIndexedAccess<'a> {
    pub(crate) object_type: Ty<'a>,
    pub(crate) index_type: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyConditional<'a> {
    /// The type being checked
    pub(crate) check_type: Ty<'a>,
    /// The type that the check type extends
    pub(crate) extends_type: Ty<'a>,
    /// The type to use if the check is true
    pub(crate) true_type: Ty<'a>,
    /// The type to use if the check is false
    pub(crate) false_type: Ty<'a>,
    /// Whether the conditional type is distributive
    ///
    /// Example: `T extends U ? X : Y` is distributive if `T` is a union type.
    pub(crate) is_distributive: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TyInfer<'a> {
    pub(crate) type_parameter: TyTypeParameter<'a>,
}

impl<'a> Ty<'a> {
    pub(crate) fn none() -> Self {
        Self::None
    }

    pub(crate) fn number() -> Self {
        Self::Number
    }

    pub(crate) fn number_literal(arena: CheckerArena<'a>, num: &'a str) -> Self {
        Self::NumberLiteral(arena.alloc(TyNumberLiteral { value: num }))
    }

    pub(crate) fn string() -> Self {
        Self::String
    }

    pub(crate) fn symbol() -> Self {
        Self::Symbol
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
        Self::BooleanLiteral(arena.alloc(TyBooleanLiteral { value: true }))
    }

    /// Literal `false` type (subtype of `boolean`)
    pub(crate) fn boolean_false(arena: CheckerArena<'a>) -> Self {
        Self::BooleanLiteral(arena.alloc(TyBooleanLiteral { value: false }))
    }

    pub(crate) fn bigint() -> Self {
        Self::Bigint
    }

    pub(crate) fn bigint_literal(arena: CheckerArena<'a>, name: &'a str) -> Self {
        Self::BigIntLiteral(arena.alloc(TyBigIntLiteral { value: name }))
    }

    pub(crate) fn template_literal(
        arena: CheckerArena<'a>,
        template: &oxc_ast::ast::TemplateLiteral<'a>,
    ) -> Self {
        Self::TemplateLiteral(
            arena.alloc(TyTemplateLiteral {
                quasis: arena.vec_from_iter(template.quasis.iter().map(|q| {
                    TemplateLiteralElement {
                        value: q.value.raw.as_str(),
                    }
                })),
                expressions: arena.vec_from_iter(
                    template
                        .expressions
                        .iter()
                        .map(|expression| Self::from_expression(expression)),
                ),
            }),
        )
    }

    pub(crate) fn ts_template_literal(
        arena: CheckerArena<'a>,
        template: &TSTemplateLiteralType<'a>,
    ) -> Self {
        Self::TemplateLiteral(
            arena.alloc(TyTemplateLiteral {
                quasis: arena.vec_from_iter(template.quasis.iter().map(|q| {
                    TemplateLiteralElement {
                        value: q.value.raw.as_str(),
                    }
                })),
                expressions: arena.vec_from_iter(
                    template
                        .types
                        .iter()
                        .map(|ty| Self::from_ts_type(arena, ty)),
                ),
            }),
        )
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

    pub(crate) fn never() -> Self {
        Self::Never
    }

    pub(crate) fn primitive_object() -> Self {
        Self::PrimitiveObject
    }

    pub(crate) fn property(name: &'a str, ty: Ty<'a>) -> TyProperty<'a> {
        TyProperty { name, ty }
    }

    pub(crate) fn parameter(name: &'a str, ty: Ty<'a>) -> TyParameter<'a> {
        TyParameter {
            name,
            ty,
            optional: false,
            rest: false,
        }
    }

    pub(crate) fn optional_parameter(name: &'a str, ty: Ty<'a>) -> TyParameter<'a> {
        TyParameter {
            name,
            ty,
            optional: true,
            rest: false,
        }
    }

    pub(crate) fn rest_parameter(name: &'a str, ty: Ty<'a>) -> TyParameter<'a> {
        TyParameter {
            name,
            ty,
            optional: false,
            rest: true,
        }
    }

    pub(crate) fn type_parameter(
        name: &'a str,
        constraint_type: Option<Ty<'a>>,
        default_type: Option<Ty<'a>>,
    ) -> TyTypeParameter<'a> {
        TyTypeParameter {
            name,
            constraint_type,
            default_type,
        }
    }

    pub(crate) fn object(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
    ) -> Self {
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(properties),
            signatures: arena.vec_from_iter(std::iter::empty()),
        }))
    }

    pub(crate) fn object_with_signatures(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
        signatures: impl IntoIterator<Item = Signature<'a>>,
    ) -> Self {
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(properties),
            signatures: arena.vec_from_iter(signatures),
        }))
    }

    pub(crate) fn module_namespace(
        arena: CheckerArena<'a>,
        name: &'a str,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
    ) -> Self {
        Self::ModuleNamespace(arena.alloc(TyModuleNamespace {
            name,
            properties: arena.vec_from_iter(properties),
        }))
    }

    pub(crate) fn function(
        arena: CheckerArena<'a>,
        type_parameters: impl IntoIterator<Item = TyTypeParameter<'a>>,
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

    pub(crate) fn string_literal(arena: CheckerArena<'a>, value: &'a str) -> Self {
        Self::StringLiteral(arena.alloc(TyStringLiteral { value }))
    }

    pub(crate) fn array(arena: CheckerArena<'a>, element_type: Ty<'a>) -> Self {
        Self::Array(arena.alloc(TyArray { element_type }))
    }

    pub(crate) fn tuple(arena: CheckerArena<'a>, elements: Vec<TupleElement<'a>>) -> Self {
        Self::Tuple(arena.alloc(TyTuple {
            elements: arena.vec_from_iter(elements),
        }))
    }

    pub(crate) fn r#union(
        arena: CheckerArena<'a>,
        types: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        reduce_union_type(arena, types)
    }

    pub(crate) fn intersection(
        arena: CheckerArena<'a>,
        types: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        Self::Intersection(arena.alloc(TyIntersection {
            types: arena.vec_from_iter(types),
        }))
    }

    pub(crate) fn keyof(arena: CheckerArena<'a>, target: Ty<'a>) -> Self {
        Self::Keyof(arena.alloc(TyKeyof { target }))
    }

    pub(crate) fn indexed_access(
        arena: CheckerArena<'a>,
        object_type: Ty<'a>,
        index_type: Ty<'a>,
    ) -> Self {
        Self::IndexedAccess(arena.alloc(TyIndexedAccess {
            object_type,
            index_type,
        }))
    }

    pub(crate) fn conditional(
        arena: CheckerArena<'a>,
        check_type: Ty<'a>,
        extends_type: Ty<'a>,
        true_type: Ty<'a>,
        false_type: Ty<'a>,
        is_distributive: bool,
    ) -> Self {
        simplify_conditional_type(
            arena,
            check_type,
            extends_type,
            true_type,
            false_type,
            is_distributive,
        )
    }

    pub(crate) fn infer(arena: CheckerArena<'a>, type_parameter: TyTypeParameter<'a>) -> Self {
        Self::Infer(arena.alloc(TyInfer { type_parameter }))
    }

    pub(crate) fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }

    pub(crate) fn is_any(&self) -> bool {
        matches!(self, Self::Any)
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
            TSType::TSSymbolKeyword(_) => Self::symbol(),
            TSType::TSUndefinedKeyword(_) => Self::undefined(),
            TSType::TSNullKeyword(_) => Self::null(),
            TSType::TSAnyKeyword(_) => Self::any(),
            TSType::TSUnknownKeyword(_) => Self::unknown(),
            TSType::TSVoidKeyword(_) => Self::void(),
            TSType::TSNeverKeyword(_) => Self::never(),
            TSType::TSObjectKeyword(_) => Self::primitive_object(),
            TSType::TSTypeLiteral(type_literal) => Self::object_with_signatures(
                arena,
                type_literal
                    .members
                    .iter()
                    .filter_map(|member| match member {
                        TSSignature::TSPropertySignature(property) => {
                            let name = property_key_name_str(&property.key)?;
                            let ty = Self::from_ts_type_annotation(
                                arena,
                                property.type_annotation.as_deref(),
                            );
                            Some(Self::property(name, ty))
                        }
                        TSSignature::TSMethodSignature(method) => {
                            let name = property_key_name_str(&method.key)?;
                            Some(Self::property(
                                name,
                                Self::function(
                                    arena,
                                    type_parameters_from_declaration(
                                        arena,
                                        method.type_parameters.as_deref(),
                                    ),
                                    function_type_parameters(
                                        arena,
                                        method.this_param.as_deref(),
                                        method.params.as_ref(),
                                    ),
                                    Self::from_ts_type_annotation(
                                        arena,
                                        method.return_type.as_deref(),
                                    ),
                                ),
                            ))
                        }
                        _ => None,
                    }),
                type_literal
                    .members
                    .iter()
                    .filter_map(|member| signature_from_ts_signature(arena, member)),
            ),
            TSType::TSArrayType(array) => {
                Self::array(arena, Self::from_ts_type(arena, &array.element_type))
            }
            TSType::TSTypeReference(reference) => Self::from_ts_type_reference(arena, reference),
            TSType::TSParenthesizedType(parenthesized) => {
                Self::from_ts_type(arena, &parenthesized.type_annotation)
            }
            TSType::TSTemplateLiteralType(template_literal) => {
                Self::ts_template_literal(arena, template_literal)
            }
            TSType::TSUnionType(r#union) => Self::r#union(
                arena,
                r#union.types.iter().map(|ty| Self::from_ts_type(arena, ty)),
            ),
            TSType::TSFunctionType(function) => Self::function(
                arena,
                type_parameters_from_declaration(arena, function.type_parameters.as_deref()),
                function_type_parameters(
                    arena,
                    function.this_param.as_deref(),
                    function.params.as_ref(),
                ),
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
                TSLiteral::TemplateLiteral(template_literal) => {
                    Self::template_literal(arena, template_literal.as_ref())
                }
                TSLiteral::UnaryExpression(_) => Ty::none(),
            },
            TSType::TSTupleType(tuple_type) => Self::tuple(
                arena,
                tuple_type
                    .element_types
                    .iter()
                    .map(|ty| match ty {
                        TSTupleElement::TSRestType(rest) => {
                            TupleElement::Rest(Self::from_ts_type(arena, &rest.type_annotation))
                        }
                        TSTupleElement::TSOptionalType(optional) => {
                            TupleElement::Optional(Self::r#union(
                                arena,
                                [
                                    Self::from_ts_type(arena, &optional.type_annotation),
                                    Self::undefined(),
                                ],
                            ))
                        }
                        _ => TupleElement::Regular(match ty.as_ts_type() {
                            Some(ts_type) => Self::from_ts_type(arena, ts_type),
                            None => Self::none(),
                        }),
                    })
                    .collect(),
            ),
            TSType::TSIntersectionType(intersection_type) => Self::intersection(
                arena,
                intersection_type
                    .types
                    .iter()
                    .map(|ty| Self::from_ts_type(arena, ty)),
            ),
            TSType::TSTypeOperatorType(operator) => match operator.operator {
                TSTypeOperatorOperator::Keyof => {
                    Self::keyof(arena, Self::from_ts_type(arena, &operator.type_annotation))
                }
                TSTypeOperatorOperator::Readonly | TSTypeOperatorOperator::Unique => Self::none(),
            },
            TSType::TSIndexedAccessType(indexed_access) => Self::indexed_access(
                arena,
                Self::from_ts_type(arena, &indexed_access.object_type),
                Self::from_ts_type(arena, &indexed_access.index_type),
            ),
            TSType::TSConditionalType(conditional) => Self::conditional(
                arena,
                Self::from_ts_type(arena, &conditional.check_type),
                Self::from_ts_type(arena, &conditional.extends_type),
                Self::from_ts_type(arena, &conditional.true_type),
                Self::from_ts_type(arena, &conditional.false_type),
                ts_type_is_naked_type_reference(&conditional.check_type),
            ),
            TSType::TSInferType(infer) => Self::infer(
                arena,
                type_parameter_from_ts_type_parameter(arena, &infer.type_parameter),
            ),
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
            Self::ModuleNamespace(namespace) => namespace
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
            )
            .with_signatures(
                arena,
                object
                    .signatures
                    .iter()
                    .map(|signature| signature.substitute_type_parameters(arena, substitutions)),
            ),
            Self::ModuleNamespace(namespace) => Self::module_namespace(
                arena,
                namespace.name,
                namespace.properties.iter().map(|property| {
                    Self::property(
                        property.name,
                        property.ty.substitute_type_parameters(arena, substitutions),
                    )
                }),
            ),
            Self::Function(function) => {
                let substitutions = substitutions
                    .iter()
                    .filter(|(name, _)| {
                        !function
                            .type_parameters
                            .iter()
                            .any(|type_parameter| type_parameter.name == **name)
                    })
                    .map(|(name, ty)| (*name, *ty))
                    .collect::<HashMap<_, _>>();
                Self::function(
                    arena,
                    function.type_parameters.iter().map(|type_parameter| {
                        Self::type_parameter(
                            type_parameter.name,
                            type_parameter.constraint_type.map(|constraint_type| {
                                constraint_type.substitute_type_parameters(arena, &substitutions)
                            }),
                            type_parameter.default_type.map(|default_type| {
                                default_type.substitute_type_parameters(arena, &substitutions)
                            }),
                        )
                    }),
                    function.parameters.iter().map(|parameter| {
                        let ty = parameter
                            .ty
                            .substitute_type_parameters(arena, &substitutions);
                        if parameter.rest {
                            Self::rest_parameter(parameter.name, ty)
                        } else if parameter.optional {
                            Self::optional_parameter(parameter.name, ty)
                        } else {
                            Self::parameter(parameter.name, ty)
                        }
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
            Self::Tuple(tuple) => Self::tuple(
                arena,
                tuple
                    .elements
                    .iter()
                    .map(|element| match element {
                        TupleElement::Regular(ty) => TupleElement::Regular(
                            ty.substitute_type_parameters(arena, substitutions),
                        ),
                        TupleElement::Rest(ty) => {
                            TupleElement::Rest(ty.substitute_type_parameters(arena, substitutions))
                        }
                        TupleElement::Optional(ty) => TupleElement::Optional(
                            ty.substitute_type_parameters(arena, substitutions),
                        ),
                    })
                    .collect(),
            ),
            Self::Union(union) => Self::r#union(
                arena,
                union
                    .types
                    .iter()
                    .map(|ty| ty.substitute_type_parameters(arena, substitutions)),
            ),
            Self::Intersection(intersection) => Self::intersection(
                arena,
                intersection
                    .types
                    .iter()
                    .map(|ty| ty.substitute_type_parameters(arena, substitutions)),
            ),
            Self::Keyof(keyof) => Self::keyof(
                arena,
                keyof
                    .target
                    .substitute_type_parameters(arena, substitutions),
            ),
            Self::IndexedAccess(indexed_access) => Self::indexed_access(
                arena,
                indexed_access
                    .object_type
                    .substitute_type_parameters(arena, substitutions),
                indexed_access
                    .index_type
                    .substitute_type_parameters(arena, substitutions),
            ),
            Self::Conditional(conditional) => {
                if conditional.is_distributive
                    && let Ty::TypeReference(reference) = conditional.check_type
                    && reference.type_arguments.is_empty()
                    && let Some(Ty::Union(union)) = substitutions.get(reference.name)
                {
                    return Self::r#union(
                        arena,
                        union.types.iter().map(|ty| {
                            let mut substitutions = substitutions.clone();
                            substitutions.insert(reference.name, *ty);
                            Self::conditional(
                                arena,
                                *ty,
                                conditional
                                    .extends_type
                                    .substitute_type_parameters(arena, &substitutions),
                                conditional
                                    .true_type
                                    .substitute_type_parameters(arena, &substitutions),
                                conditional
                                    .false_type
                                    .substitute_type_parameters(arena, &substitutions),
                                false,
                            )
                        }),
                    );
                }

                Self::conditional(
                    arena,
                    conditional
                        .check_type
                        .substitute_type_parameters(arena, substitutions),
                    conditional
                        .extends_type
                        .substitute_type_parameters(arena, substitutions),
                    conditional
                        .true_type
                        .substitute_type_parameters(arena, substitutions),
                    conditional
                        .false_type
                        .substitute_type_parameters(arena, substitutions),
                    conditional.is_distributive,
                )
            }
            Self::Infer(infer) => {
                // TODO(correctness): Treat `infer` as a scoped binding site for conditional
                // type matching instead of only preserving its syntax.
                Self::infer(
                    arena,
                    Self::type_parameter(
                        infer.type_parameter.name,
                        infer.type_parameter.constraint_type.map(|constraint_type| {
                            constraint_type.substitute_type_parameters(arena, substitutions)
                        }),
                        infer.type_parameter.default_type.map(|default_type| {
                            default_type.substitute_type_parameters(arena, substitutions)
                        }),
                    ),
                )
            }
            _ => *self,
        }
    }

    #[cfg(debug_assertions)]
    pub(crate) fn enum_variant_name(self) -> &'static str {
        match self {
            Self::None => "TyNone",
            Self::Number => "TyNumber",
            Self::String => "TyString",
            Self::Boolean => "TyBoolean",
            Self::Bigint => "TyBigint",
            Self::Symbol => "TySymbol",
            Self::Undefined => "TyUndefined",
            Self::Null => "TyNull",
            Self::Any => "TyAny",
            Self::Unknown => "TyUnknown",
            Self::Void => "TyVoid",
            Self::Never => "TyNever",
            Self::Object(_) => "TyObject",
            Self::ModuleNamespace(_) => "TyModuleNamespace",
            Self::PrimitiveObject => "TyPrimitiveObject",
            Self::Function(_) => "TyFunction",
            Self::TypeReference(_) => "TyTypeReference",
            Self::StringLiteral(_) => "TyStringLiteral",
            Self::NumberLiteral(_) => "TyNumberLiteral",
            Self::BooleanLiteral(_) => "TyBooleanLiteral",
            Self::BigIntLiteral(_) => "TyBigIntLiteral",
            Self::TemplateLiteral(_) => "TyTemplateLiteral",
            Self::Array(_) => "TyArray",
            Self::Tuple(_) => "TyTuple",
            Self::Union(_) => "TyUnion",
            Self::Intersection(_) => "TyIntersection",
            Self::Keyof(_) => "TyKeyof",
            Self::IndexedAccess(_) => "TyIndexedAccess",
            Self::Conditional(_) => "TyConditional",
            Self::Infer(_) => "TyInfer",
        }
    }

    pub(crate) fn to_type_string(self) -> String {
        match self {
            Self::None => "none".to_string(),
            Self::Number => "number".to_string(),
            Self::String => "string".to_string(),
            Self::Boolean => "boolean".to_string(),
            Self::Bigint => "bigint".to_string(),
            Self::Symbol => "symbol".to_string(),
            Self::Undefined => "undefined".to_string(),
            Self::Null => "null".to_string(),
            Self::Any => "any".to_string(),
            Self::Unknown => "unknown".to_string(),
            Self::Void => "void".to_string(),
            Self::Never => "never".to_string(),
            Self::PrimitiveObject => "object".to_string(),
            Self::Object(object) => {
                if object.properties.is_empty() && object.signatures.is_empty() {
                    return "{}".to_string();
                }

                let members = object
                    .signatures
                    .iter()
                    .map(|signature| signature.to_type_string())
                    .chain(object.properties.iter().map(|property| {
                        format!("{}: {};", property.name, property.ty.to_type_string())
                    }))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("{{ {members} }}")
            }
            Self::ModuleNamespace(namespace) => format!("typeof {}", namespace.name),
            Self::Function(function) => function_type_to_string(function),
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
            Self::StringLiteral(string_literal) => {
                let content = string_literal
                    .value
                    .strip_prefix('\'')
                    .and_then(|name| name.strip_suffix('\''))
                    .or_else(|| {
                        string_literal
                            .value
                            .strip_prefix('"')
                            .and_then(|name| name.strip_suffix('"'))
                    })
                    .unwrap_or(string_literal.value);
                format!("{content:?}")
            }
            Self::NumberLiteral(number_literal) => number_literal.value.to_string(),
            Self::BooleanLiteral(boolean_literal) => boolean_literal.value.to_string(),
            Self::BigIntLiteral(big_int_literal) => format!("{}n", big_int_literal.value),
            Self::TemplateLiteral(template_literal) => {
                let mut repr = String::from("`");

                for (index, quasi) in template_literal.quasis.iter().enumerate() {
                    repr.push_str(quasi.value);
                    if let Some(expression) = template_literal.expressions.get(index) {
                        repr.push_str("${");
                        repr.push_str(&expression.to_type_string());
                        repr.push('}');
                    }
                }

                if template_literal.expressions.len() > template_literal.quasis.len() {
                    for expression in template_literal
                        .expressions
                        .iter()
                        .skip(template_literal.quasis.len())
                    {
                        repr.push_str("${");
                        repr.push_str(&expression.to_type_string());
                        repr.push('}');
                    }
                }

                repr.push('`');
                repr
            }
            Self::Array(array) => {
                let element_type = array.element_type.to_type_string();
                if array.element_type.display_needs_parentheses() {
                    format!("({element_type})[]")
                } else {
                    format!("{element_type}[]")
                }
            }
            Self::Tuple(tuple) => {
                let elements = tuple
                    .elements
                    .iter()
                    .map(|element| match element {
                        TupleElement::Regular(ty) => ty.to_type_string(),
                        TupleElement::Rest(ty) => format!("...{}", ty.to_type_string()),
                        TupleElement::Optional(ty) => {
                            let ty = ty.to_type_string();
                            if element_type_needs_parentheses(element) {
                                format!("({ty})?")
                            } else {
                                format!("{ty}?")
                            }
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("[{elements}]")
            }
            Self::Union(union) => union
                .types
                .iter()
                .map(|ty| {
                    let type_string = ty.to_type_string();
                    if matches!(ty, Ty::Function(_)) {
                        format!("({type_string})")
                    } else {
                        type_string
                    }
                })
                .collect::<Vec<_>>()
                .join(" | "),
            Self::Intersection(intersection) => intersection
                .types
                .iter()
                .map(|ty| {
                    let type_string = ty.to_type_string();
                    if matches!(ty, Ty::Function(_)) {
                        format!("({type_string})")
                    } else {
                        type_string
                    }
                })
                .collect::<Vec<_>>()
                .join(" & "),
            Self::Keyof(keyof) => {
                let target = keyof.target.to_type_string();
                if keyof.target.type_operator_needs_parentheses() {
                    format!("keyof ({target})")
                } else {
                    format!("keyof {target}")
                }
            }
            Self::IndexedAccess(indexed_access) => {
                let object_type = indexed_access.object_type.to_type_string();
                let index_type = indexed_access.index_type.to_type_string();
                if indexed_access
                    .object_type
                    .indexed_access_needs_parentheses()
                {
                    format!("({object_type})[{index_type}]")
                } else {
                    format!("{object_type}[{index_type}]")
                }
            }
            Self::Conditional(conditional) => {
                let check_type = conditional.check_type.to_type_string();
                let extends_type = conditional.extends_type.to_type_string();
                let check_type = if conditional.check_type.conditional_type_needs_parentheses() {
                    format!("({check_type})")
                } else {
                    check_type
                };
                let extends_type = if conditional
                    .extends_type
                    .conditional_type_needs_parentheses()
                {
                    format!("({extends_type})")
                } else {
                    extends_type
                };
                format!(
                    "{check_type} extends {extends_type} ? {} : {}",
                    conditional.true_type.to_type_string(),
                    conditional.false_type.to_type_string()
                )
            }
            Self::Infer(infer) => format!(
                "infer {}",
                type_parameter_to_type_string(&infer.type_parameter)
            ),
        }
    }

    /// Whether this type needs parentheses when printed
    fn display_needs_parentheses(&self) -> bool {
        matches!(
            self,
            Self::Function(_) | Self::Union(_) | Self::Conditional(_)
        )
    }

    fn type_operator_needs_parentheses(&self) -> bool {
        matches!(
            self,
            Self::Function(_) | Self::Union(_) | Self::Intersection(_) | Self::Conditional(_)
        )
    }

    fn indexed_access_needs_parentheses(&self) -> bool {
        matches!(
            self,
            Self::Function(_) | Self::Union(_) | Self::Intersection(_) | Self::Conditional(_)
        )
    }

    fn conditional_type_needs_parentheses(&self) -> bool {
        matches!(
            self,
            Self::Function(_) | Self::Union(_) | Self::Intersection(_) | Self::Conditional(_)
        )
    }

    fn with_signatures(
        self,
        arena: CheckerArena<'a>,
        signatures: impl IntoIterator<Item = Signature<'a>>,
    ) -> Self {
        let Self::Object(object) = self else {
            return self;
        };
        Self::object_with_signatures(arena, object.properties.iter().copied(), signatures)
    }
}

fn simplify_conditional_type<'a>(
    arena: CheckerArena<'a>,
    check_type: Ty<'a>,
    extends_type: Ty<'a>,
    true_type: Ty<'a>,
    false_type: Ty<'a>,
    is_distributive: bool,
) -> Ty<'a> {
    if contains_infer(check_type) || contains_infer(extends_type) {
        // TODO(correctness): Match `check_type` against `extends_type`, collect `infer`
        // substitutions, and apply them to the true branch.
        return Ty::Conditional(arena.alloc(TyConditional {
            check_type,
            extends_type,
            true_type,
            false_type,
            is_distributive,
        }));
    }

    if contains_unresolved_type_variable(check_type)
        || contains_unresolved_type_variable(extends_type)
    {
        return Ty::Conditional(arena.alloc(TyConditional {
            check_type,
            extends_type,
            true_type,
            false_type,
            is_distributive,
        }));
    }

    if crate::relations::is_assignable_to(check_type, extends_type) {
        true_type
    } else {
        false_type
    }
}

fn contains_unresolved_type_variable(ty: Ty<'_>) -> bool {
    match ty {
        Ty::TypeReference(reference) => {
            reference.type_arguments.is_empty()
                || reference
                    .type_arguments
                    .iter()
                    .any(|ty| contains_unresolved_type_variable(*ty))
        }
        Ty::Object(object) => {
            object
                .properties
                .iter()
                .any(|property| contains_unresolved_type_variable(property.ty))
                || object.signatures.iter().any(|signature| {
                    signature
                        .function
                        .parameters
                        .iter()
                        .any(|parameter| contains_unresolved_type_variable(parameter.ty))
                        || contains_unresolved_type_variable(signature.function.return_type)
                })
        }
        Ty::ModuleNamespace(namespace) => namespace
            .properties
            .iter()
            .any(|property| contains_unresolved_type_variable(property.ty)),
        Ty::Function(function) => {
            function
                .parameters
                .iter()
                .any(|parameter| contains_unresolved_type_variable(parameter.ty))
                || contains_unresolved_type_variable(function.return_type)
        }
        Ty::TemplateLiteral(template_literal) => template_literal
            .expressions
            .iter()
            .any(|ty| contains_unresolved_type_variable(*ty)),
        Ty::Array(array) => contains_unresolved_type_variable(array.element_type),
        Ty::Tuple(tuple) => tuple.elements.iter().any(|element| match element {
            TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => {
                contains_unresolved_type_variable(*ty)
            }
        }),
        Ty::Union(union) => union
            .types
            .iter()
            .any(|ty| contains_unresolved_type_variable(*ty)),
        Ty::Intersection(intersection) => intersection
            .types
            .iter()
            .any(|ty| contains_unresolved_type_variable(*ty)),
        Ty::Keyof(keyof) => contains_unresolved_type_variable(keyof.target),
        Ty::IndexedAccess(indexed_access) => {
            contains_unresolved_type_variable(indexed_access.object_type)
                || contains_unresolved_type_variable(indexed_access.index_type)
        }
        Ty::Conditional(conditional) => {
            contains_unresolved_type_variable(conditional.check_type)
                || contains_unresolved_type_variable(conditional.extends_type)
                || contains_unresolved_type_variable(conditional.true_type)
                || contains_unresolved_type_variable(conditional.false_type)
        }
        Ty::Infer(_) => true,
        _ => false,
    }
}

fn contains_infer(ty: Ty<'_>) -> bool {
    match ty {
        Ty::Infer(_) => true,
        Ty::Object(object) => {
            object
                .properties
                .iter()
                .any(|property| contains_infer(property.ty))
                || object.signatures.iter().any(|signature| {
                    signature
                        .function
                        .parameters
                        .iter()
                        .any(|parameter| contains_infer(parameter.ty))
                        || contains_infer(signature.function.return_type)
                })
        }
        Ty::ModuleNamespace(namespace) => namespace
            .properties
            .iter()
            .any(|property| contains_infer(property.ty)),
        Ty::Function(function) => {
            function
                .parameters
                .iter()
                .any(|parameter| contains_infer(parameter.ty))
                || contains_infer(function.return_type)
        }
        Ty::TypeReference(reference) => reference
            .type_arguments
            .iter()
            .any(|ty| contains_infer(*ty)),
        Ty::TemplateLiteral(template_literal) => template_literal
            .expressions
            .iter()
            .any(|ty| contains_infer(*ty)),
        Ty::Array(array) => contains_infer(array.element_type),
        Ty::Tuple(tuple) => tuple.elements.iter().any(|element| match element {
            TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => {
                contains_infer(*ty)
            }
        }),
        Ty::Union(union) => union.types.iter().any(|ty| contains_infer(*ty)),
        Ty::Intersection(intersection) => intersection.types.iter().any(|ty| contains_infer(*ty)),
        Ty::Keyof(keyof) => contains_infer(keyof.target),
        Ty::IndexedAccess(indexed_access) => {
            contains_infer(indexed_access.object_type) || contains_infer(indexed_access.index_type)
        }
        Ty::Conditional(conditional) => {
            contains_infer(conditional.check_type)
                || contains_infer(conditional.extends_type)
                || contains_infer(conditional.true_type)
                || contains_infer(conditional.false_type)
        }
        _ => false,
    }
}

fn ts_type_is_naked_type_reference(ty: &TSType<'_>) -> bool {
    matches!(
        ty,
        TSType::TSTypeReference(reference) if reference.type_arguments.is_none()
    )
}

pub(crate) fn reduce_union_type<'a>(
    arena: CheckerArena<'a>,
    types: impl IntoIterator<Item = Ty<'a>>,
) -> Ty<'a> {
    let mut type_set = Vec::new();
    for ty in types {
        add_type_to_union(&mut type_set, ty);
    }

    if type_set.iter().any(|ty| matches!(ty, Ty::Any)) {
        return Ty::any();
    }
    if type_set.iter().any(|ty| matches!(ty, Ty::Unknown)) {
        return Ty::unknown();
    }

    remove_redundant_literal_types(&mut type_set);

    if type_set.len() == 1 {
        return type_set[0];
    }

    Ty::Union(arena.alloc(TyUnion {
        types: arena.vec_from_iter(type_set),
    }))
}

fn add_type_to_union<'a>(type_set: &mut Vec<Ty<'a>>, ty: Ty<'a>) {
    if let Ty::Union(union) = ty {
        for ty in &union.types {
            add_type_to_union(type_set, *ty);
        }
    } else if !type_set.contains(&ty) {
        type_set.push(ty);
    }
}

fn remove_redundant_literal_types(type_set: &mut Vec<Ty<'_>>) {
    let has_string = type_set.iter().any(|ty| matches!(ty, Ty::String));
    let has_number = type_set.iter().any(|ty| matches!(ty, Ty::Number));
    let has_boolean = type_set.iter().any(|ty| matches!(ty, Ty::Boolean));
    let has_bigint = type_set.iter().any(|ty| matches!(ty, Ty::Bigint));

    type_set.retain(|ty| match ty {
        Ty::StringLiteral(_) | Ty::TemplateLiteral(_) => !has_string,
        Ty::NumberLiteral(_) => !has_number,
        Ty::BooleanLiteral(_) => !has_boolean,
        Ty::BigIntLiteral(_) => !has_bigint,
        _ => true,
    });
}

fn element_type_needs_parentheses(element: &TupleElement<'_>) -> bool {
    match element {
        TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => {
            ty.display_needs_parentheses()
        }
    }
}

fn type_parameter_to_type_string(type_parameter: &TyTypeParameter<'_>) -> String {
    let mut type_string = type_parameter.name.to_string();
    if let Some(constraint_type) = type_parameter.constraint_type {
        type_string.push_str(" extends ");
        type_string.push_str(&constraint_type.to_type_string());
    }
    if let Some(default_type) = type_parameter.default_type {
        type_string.push_str(" = ");
        type_string.push_str(&default_type.to_type_string());
    }
    type_string
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum SignatureKind {
    Call,
    Construct,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct Signature<'a> {
    pub(crate) kind: SignatureKind,
    pub(crate) function: &'a TyFunction<'a>,
}

impl<'a> Signature<'a> {
    pub(crate) fn new(kind: SignatureKind, function: &'a TyFunction<'a>) -> Self {
        Self { kind, function }
    }

    pub(crate) fn substitute_type_parameters(
        self,
        arena: CheckerArena<'a>,
        substitutions: &HashMap<&'a str, Ty<'a>>,
    ) -> Self {
        let Ty::Function(function) =
            Ty::Function(self.function).substitute_type_parameters(arena, substitutions)
        else {
            unreachable!("signature substitution preserves function type")
        };
        Self::new(self.kind, function)
    }

    pub(crate) fn to_type_string(self) -> String {
        match self.kind {
            SignatureKind::Call => format!("{};", signature_to_type_string(self.function)),
            SignatureKind::Construct => {
                format!("new {};", signature_to_type_string(self.function))
            }
        }
    }
}

pub(crate) struct IndexInfo {}

fn function_type_to_string(function: &TyFunction<'_>) -> String {
    let (type_parameters, parameters) = function_type_head_to_string(function);
    format!(
        "{type_parameters}({parameters}) => {}",
        function.return_type.to_type_string()
    )
}

fn signature_to_type_string(function: &TyFunction<'_>) -> String {
    let (type_parameters, parameters) = function_type_head_to_string(function);
    format!(
        "{type_parameters}({parameters}): {}",
        function.return_type.to_type_string()
    )
}

fn function_type_head_to_string(function: &TyFunction<'_>) -> (String, String) {
    let type_parameters = if function.type_parameters.is_empty() {
        String::new()
    } else {
        let type_parameters = function
            .type_parameters
            .iter()
            .map(type_parameter_to_type_string)
            .collect::<Vec<_>>()
            .join(", ");
        format!("<{type_parameters}>")
    };
    let parameters = function
        .parameters
        .iter()
        .map(|parameter| {
            if parameter.rest {
                format!("...{}: {}", parameter.name, parameter.ty.to_type_string())
            } else if parameter.optional {
                format!("{}?: {}", parameter.name, parameter.ty.to_type_string())
            } else {
                format!("{}: {}", parameter.name, parameter.ty.to_type_string())
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    (type_parameters, parameters)
}

fn signature_from_ts_signature<'a>(
    arena: CheckerArena<'a>,
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
    let Ty::Function(function) = Ty::function(
        arena,
        type_parameters_from_declaration(arena, type_parameters),
        function_type_parameters(arena, this_param, parameters),
        return_type.map_or_else(Ty::any, |return_type| {
            Ty::from_ts_type_annotation(arena, Some(return_type))
        }),
    ) else {
        unreachable!("signature construction always creates a function type")
    };
    Some(Signature::new(kind, function))
}

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

pub(crate) fn type_parameters_from_declaration<'a>(
    arena: CheckerArena<'a>,
    declaration: Option<&TSTypeParameterDeclaration<'a>>,
) -> Vec<TyTypeParameter<'a>> {
    declaration.map_or_else(Vec::new, |declaration| {
        declaration
            .params
            .iter()
            .map(|parameter| type_parameter_from_ts_type_parameter(arena, parameter))
            .collect()
    })
}

pub(crate) fn type_parameter_from_ts_type_parameter<'a>(
    arena: CheckerArena<'a>,
    parameter: &TSTypeParameter<'a>,
) -> TyTypeParameter<'a> {
    Ty::type_parameter(
        parameter.name.name.as_str(),
        parameter
            .constraint
            .as_ref()
            .map(|constraint_type| Ty::from_ts_type(arena, constraint_type)),
        parameter
            .default
            .as_ref()
            .map(|default_type| Ty::from_ts_type(arena, default_type)),
    )
}

fn function_type_parameters<'a>(
    arena: CheckerArena<'a>,
    this_param: Option<&TSThisParameter<'a>>,
    params: &oxc_ast::ast::FormalParameters<'a>,
) -> Vec<TyParameter<'a>> {
    this_param
        .iter()
        .map(|parameter| function_type_this_parameter(arena, parameter))
        .chain(
            params
                .items
                .iter()
                .map(|parameter| function_type_parameter(arena, parameter)),
        )
        .chain(
            params
                .rest
                .iter()
                .map(|parameter| function_type_rest_parameter(arena, parameter)),
        )
        .collect()
}

fn function_type_this_parameter<'a>(
    arena: CheckerArena<'a>,
    parameter: &TSThisParameter<'a>,
) -> TyParameter<'a> {
    Ty::parameter(
        "this",
        Ty::from_ts_type_annotation(arena, parameter.type_annotation.as_deref()),
    )
}

fn function_type_parameter<'a>(
    arena: CheckerArena<'a>,
    parameter: &FormalParameter<'a>,
) -> TyParameter<'a> {
    let name = binding_pattern_name_str(&parameter.pattern).unwrap_or("_");
    let ty = Ty::from_ts_type_annotation(arena, parameter.type_annotation.as_deref());
    if parameter.optional {
        Ty::optional_parameter(name, ty)
    } else {
        Ty::parameter(name, ty)
    }
}

fn function_type_rest_parameter<'a>(
    arena: CheckerArena<'a>,
    parameter: &FormalParameterRest<'a>,
) -> TyParameter<'a> {
    let name = binding_pattern_name_str(&parameter.rest.argument).unwrap_or("_");
    Ty::rest_parameter(
        name,
        Ty::from_ts_type_annotation(arena, parameter.type_annotation.as_deref()),
    )
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

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_allocator::Allocator;

    fn arena(allocator: &Allocator) -> CheckerArena<'_> {
        CheckerArena::new(allocator)
    }

    #[test]
    fn union_reduction_absorbs_any_and_unknown() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);

        assert_eq!(Ty::r#union(arena, [Ty::any(), Ty::undefined()]), Ty::any());
        assert_eq!(
            Ty::r#union(arena, [Ty::unknown(), Ty::undefined(), Ty::string()]),
            Ty::unknown()
        );
        assert_eq!(Ty::r#union(arena, [Ty::unknown(), Ty::any()]), Ty::any());
    }

    #[test]
    fn union_reduction_collapses_literals_to_primitive_types() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);

        assert_eq!(
            Ty::r#union(arena, [Ty::number_literal(arena, "1"), Ty::number()]),
            Ty::number()
        );
        assert_eq!(
            Ty::r#union(arena, [Ty::string_literal(arena, "ready"), Ty::string()]),
            Ty::string()
        );
        assert_eq!(
            Ty::r#union(arena, [Ty::boolean_true(arena), Ty::boolean()]),
            Ty::boolean()
        );
        assert_eq!(
            Ty::r#union(arena, [Ty::bigint_literal(arena, "1"), Ty::bigint()]),
            Ty::bigint()
        );
    }

    #[test]
    fn union_reduction_flattens_deduplicates_and_returns_singletons() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let nested = Ty::r#union(arena, [Ty::number(), Ty::string()]);

        assert_eq!(
            Ty::r#union(arena, [nested, Ty::number(), Ty::string()]),
            nested
        );
        assert_eq!(
            Ty::r#union(arena, [Ty::number(), Ty::number()]),
            Ty::number()
        );
    }

    #[test]
    fn union_reduction_preserves_distinct_non_redundant_types() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);

        assert_eq!(
            Ty::r#union(arena, [Ty::number(), Ty::undefined()]).to_type_string(),
            "number | undefined"
        );
        assert_eq!(
            Ty::r#union(arena, [Ty::void(), Ty::undefined()]).to_type_string(),
            "void | undefined"
        );
    }

    #[test]
    fn union_display_parenthesizes_function_members() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let a1 = Ty::type_reference(arena, "A1", []);
        let r = Ty::type_reference(arena, "R", []);
        let function = Ty::function(arena, [], [Ty::parameter("arg1", a1)], r);

        assert_eq!(
            Ty::r#union(arena, [function, Ty::null(), Ty::undefined()]).to_type_string(),
            "((arg1: A1) => R) | null | undefined"
        );
    }
}
