use oxc_allocator::{Allocator, Vec as ArenaVec};
use oxc_ast::ast::{
    BindingPattern, Expression, PropertyKey, TSMappedTypeModifierOperator, TSTemplateLiteralType,
    TSType, TSTypeAnnotation, TSTypePredicate, TSTypePredicateName,
};
use std::collections::HashMap;

use crate::type_set::reduce_union_type;

#[derive(Clone, Copy)]
pub struct CheckerArena<'a> {
    allocator: &'a Allocator,
}

impl<'a> CheckerArena<'a> {
    pub fn new(allocator: &'a Allocator) -> Self {
        Self { allocator }
    }

    pub(crate) fn alloc<T>(&self, value: T) -> &'a T {
        self.allocator.alloc(value)
    }

    pub(crate) fn str(&self, value: &str) -> &'a str {
        self.allocator.alloc_str(value)
    }

    pub(crate) fn vec_from_iter<T>(&self, iter: impl IntoIterator<Item = T>) -> ArenaVec<'a, T> {
        ArenaVec::from_iter_in(iter, self.allocator)
    }
}

#[repr(C, u8)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Ty<'a> {
    None,
    Number,
    String,
    Boolean,
    Bigint,
    Symbol,
    UniqueSymbol(&'a TyUniqueSymbol<'a>),
    Undefined,
    Null,
    Any,
    Unknown,
    Void,
    Never,
    /// Primitive `object` keyword (not to be confused with `{}`)
    PrimitiveObject,
    This,
    Object(&'a TyObject<'a>),
    ModuleNamespace(&'a TyModuleNamespace<'a>),
    Function(&'a TyFunction<'a>),
    TypeReference(&'a TyTypeReference<'a>),
    /// `typeof X` / `typeof X<U>` query against a value-side symbol.
    TypeQuery(&'a TyTypeQuery<'a>),
    StringLiteral(&'a TyStringLiteral<'a>),
    NumberLiteral(&'a TyNumberLiteral<'a>),
    BooleanLiteral(bool),
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
    /// Mapped type, e.g. `{ [P in keyof T]: T[P] }` or `{ readonly [P in K as N]?: V }`.
    Mapped(&'a TyMapped<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyObject<'a> {
    pub(crate) properties: ArenaVec<'a, TyProperty<'a>>,
    pub(crate) signatures: ArenaVec<'a, Signature<'a>>,
    pub(crate) index_infos: ArenaVec<'a, IndexInfo<'a>>,
}

impl<'a> TyObject<'a> {
    /// Returns `true` if the object has no properties, signatures, or index infos.
    fn is_empty(&self) -> bool {
        self.properties.is_empty() && self.signatures.is_empty() && self.index_infos.is_empty()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyModuleNamespace<'a> {
    pub(crate) name: &'a str,
    pub(crate) properties: ArenaVec<'a, TyProperty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyProperty<'a> {
    pub(crate) name: &'a str,
    pub(crate) ty: Ty<'a>,
    pub(crate) computed: bool,
    pub(crate) optional: bool,
    pub(crate) method: bool,
    pub(crate) readonly: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyFunction<'a> {
    pub(crate) type_parameters: ArenaVec<'a, TyTypeParameter<'a>>,
    pub(crate) parameters: ArenaVec<'a, TyParameter<'a>>,
    pub(crate) return_type: Ty<'a>,
    pub(crate) type_predicate: Option<&'a TyTypePredicate<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum TyTypePredicateKind {
    This,
    Identifier,
    AssertsThis,
    AssertsIdentifier,
}

impl TyTypePredicateKind {
    fn is_asserts(self) -> bool {
        matches!(self, Self::AssertsThis | Self::AssertsIdentifier)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyTypePredicate<'a> {
    pub(crate) kind: TyTypePredicateKind,
    pub(crate) parameter_name: Option<&'a str>,
    pub(crate) parameter_index: Option<usize>,
    pub(crate) target_type: Option<Ty<'a>>,
}

impl<'a> TyTypePredicate<'a> {
    pub(crate) fn substitute_type_parameters(
        self,
        arena: CheckerArena<'a>,
        substitutions: &HashMap<&'a str, Ty<'a>>,
    ) -> Self {
        Self {
            kind: self.kind,
            parameter_name: self.parameter_name,
            parameter_index: self.parameter_index,
            target_type: self
                .target_type
                .map(|ty| ty.substitute_type_parameters(arena, substitutions)),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyTypeParameter<'a> {
    pub(crate) name: &'a str,
    /// constraint type (e.g., `U` in `T extends U`)
    pub(crate) constraint_type: Option<Ty<'a>>,
    pub(crate) default_type: Option<Ty<'a>>,
    // TODO: This should probably be a flag.
    /// Whether to display the default type when printing. This can be used to
    /// omit the default type in lib declarations.
    pub(crate) display_default: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyParameter<'a> {
    pub(crate) name: &'a str,
    pub(crate) ty: Ty<'a>,
    pub(crate) optional: bool,
    pub(crate) rest: bool,
}

#[derive(Debug, Eq)]
pub struct TyTypeReference<'a> {
    pub(crate) name: &'a str,
    pub(crate) type_arguments: ArenaVec<'a, Ty<'a>>,
    pub(crate) explicit_type_argument_count: usize,
}

impl PartialEq for TyTypeReference<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.type_arguments == other.type_arguments
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyTypeQuery<'a> {
    /// Display name of the queried entity (e.g. `"Foo"`, `"Foo.Bar"`, `"this"`).
    pub(crate) name: &'a str,
    /// The type of the queried symbol.
    pub(crate) resolved: Ty<'a>,
    /// Explicit type arguments on the query (e.g. `<U>` in `typeof Err<U>`).
    pub(crate) type_arguments: ArenaVec<'a, Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyStringLiteral<'a> {
    pub(crate) value: &'a str,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyNumberLiteral<'a> {
    // TODO(ast): use a number type?
    pub(crate) value: &'a str,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyBigIntLiteral<'a> {
    // TODO(ast): use a number type?
    pub(crate) value: &'a str,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyUniqueSymbol<'a> {
    pub(crate) name: Option<&'a str>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyTemplateLiteral<'a> {
    pub(crate) quasis: ArenaVec<'a, TemplateLiteralElement<'a>>,
    pub(crate) expressions: ArenaVec<'a, Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) struct TemplateLiteralElement<'a> {
    pub(crate) value: &'a str,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyArray<'a> {
    pub(crate) element_type: Ty<'a>,
    /// `true` when produced from `readonly T[]` or `ReadonlyArray<T>`.
    pub(crate) readonly: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyTuple<'a> {
    pub(crate) elements: ArenaVec<'a, TupleElement<'a>>,
    /// `true` when produced from a `readonly` tuple literal.
    pub(crate) readonly: bool,
}

/// A tuple element is either: a regular type [`Ty`], a rest type, or an optional type.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TupleElement<'a> {
    /// A regular tuple element, like `string` in `[string, number]`.
    Regular(Ty<'a>),
    /// A rest tuple element, like `string[]` in `[string, ...string[]]`.
    Rest(Ty<'a>),
    /// An optional tuple element, like `number?` in `[string, number?]`.
    Optional(Ty<'a>),
}

impl<'a> TupleElement<'a> {
    /// Returns the type of this tuple element.
    pub(crate) fn ty(&self) -> Ty<'a> {
        match self {
            TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => *ty,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyUnion<'a> {
    pub(crate) types: ArenaVec<'a, Ty<'a>>,
    // TODO: Add flags
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyIntersection<'a> {
    pub(crate) types: ArenaVec<'a, Ty<'a>>,
    // TODO: Add flags
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyKeyof<'a> {
    pub(crate) target: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyIndexedAccess<'a> {
    pub(crate) object_type: Ty<'a>,
    pub(crate) index_type: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyConditional<'a> {
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
pub struct TyInfer<'a> {
    pub(crate) type_parameter: TyTypeParameter<'a>,
}

/// Mapped type, mirroring typescript-go's `MappedType` shape.
#[derive(Debug, PartialEq, Eq)]
pub struct TyMapped<'a> {
    /// Name of the key type parameter (the `P` in `[P in K]`).
    pub(crate) key: &'a str,
    /// Constraint of the key (the `K` in `[P in K]`).
    pub(crate) constraint: Ty<'a>,
    /// Optional `as N` key remapping type.
    pub(crate) name_type: Option<Ty<'a>>,
    /// Value type (right-hand side of the index signature).
    pub(crate) template: Ty<'a>,
    /// Optional modifier on the value (`?`, `+?`, `-?`).
    pub(crate) optional: MappedModifier,
    /// Readonly modifier on the index signature (`readonly`, `+readonly`, `-readonly`).
    pub(crate) readonly: MappedModifier,
}

/// Presence/polarity of a `readonly` or `?` modifier on a mapped type.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum MappedModifier {
    None,
    True,
    Plus,
    Minus,
}

impl MappedModifier {
    pub(crate) fn from_ast(op: Option<TSMappedTypeModifierOperator>) -> Self {
        match op {
            None => Self::None,
            Some(TSMappedTypeModifierOperator::True) => Self::True,
            Some(TSMappedTypeModifierOperator::Plus) => Self::Plus,
            Some(TSMappedTypeModifierOperator::Minus) => Self::Minus,
        }
    }
}

impl<'a> Ty<'a> {
    pub fn none() -> Self {
        Self::None
    }

    pub fn number() -> Self {
        Self::Number
    }

    pub fn number_literal(arena: CheckerArena<'a>, num: &'a str) -> Self {
        Self::NumberLiteral(arena.alloc(TyNumberLiteral { value: num }))
    }

    pub fn string() -> Self {
        Self::String
    }

    pub fn symbol() -> Self {
        Self::Symbol
    }

    pub fn unique_symbol(arena: CheckerArena<'a>, name: Option<&'a str>) -> Self {
        Self::UniqueSymbol(arena.alloc(TyUniqueSymbol { name }))
    }

    /// General `boolean` type (true or false)
    pub fn boolean() -> Self {
        Self::Boolean
    }

    /// Literal `boolean` type (`true` or `false`), subtype of `boolean`
    pub fn boolean_literal(value: bool) -> Self {
        if value {
            Self::boolean_true()
        } else {
            Self::boolean_false()
        }
    }

    /// Literal `true` type (subtype of `boolean`)
    pub fn boolean_true() -> Self {
        Self::BooleanLiteral(true)
    }

    /// Literal `false` type (subtype of `boolean`)
    pub fn boolean_false() -> Self {
        Self::BooleanLiteral(false)
    }

    pub fn bigint() -> Self {
        Self::Bigint
    }

    pub fn bigint_literal(arena: CheckerArena<'a>, name: &'a str) -> Self {
        Self::BigIntLiteral(arena.alloc(TyBigIntLiteral { value: name }))
    }

    pub fn template_literal(
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

    pub fn ts_template_literal(
        arena: CheckerArena<'a>,
        template: &TSTemplateLiteralType<'a>,
        expressions: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        Self::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter(template.quasis.iter().map(|q| TemplateLiteralElement {
                value: q.value.raw.as_str(),
            })),
            expressions: arena.vec_from_iter(expressions),
        }))
    }

    pub fn undefined() -> Self {
        Self::Undefined
    }

    pub fn null() -> Self {
        Self::Null
    }

    pub fn any() -> Self {
        Self::Any
    }

    pub fn unknown() -> Self {
        Self::Unknown
    }

    pub fn void() -> Self {
        Self::Void
    }

    pub fn never() -> Self {
        Self::Never
    }

    pub fn primitive_object() -> Self {
        Self::PrimitiveObject
    }

    pub fn this() -> Self {
        Self::This
    }

    pub fn property(name: &'a str, ty: Ty<'a>) -> TyProperty<'a> {
        TyProperty {
            name,
            computed: false,
            optional: false,
            method: false,
            readonly: false,
            ty,
        }
    }

    pub fn parameter(name: &'a str, ty: Ty<'a>) -> TyParameter<'a> {
        TyParameter {
            name,
            ty,
            optional: false,
            rest: false,
        }
    }

    pub fn optional_parameter(name: &'a str, ty: Ty<'a>) -> TyParameter<'a> {
        TyParameter {
            name,
            ty,
            optional: true,
            rest: false,
        }
    }

    pub fn rest_parameter(name: &'a str, ty: Ty<'a>) -> TyParameter<'a> {
        TyParameter {
            name,
            ty,
            optional: false,
            rest: true,
        }
    }

    pub fn type_parameter(
        name: &'a str,
        constraint_type: Option<Ty<'a>>,
        default_type: Option<Ty<'a>>,
    ) -> TyTypeParameter<'a> {
        Self::type_parameter_with_display_default(name, constraint_type, default_type, true)
    }

    pub fn type_parameter_with_display_default(
        name: &'a str,
        constraint_type: Option<Ty<'a>>,
        default_type: Option<Ty<'a>>,
        display_default: bool,
    ) -> TyTypeParameter<'a> {
        TyTypeParameter {
            name,
            constraint_type,
            default_type,
            display_default,
        }
    }

    pub fn object(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
    ) -> Self {
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(properties),
            signatures: arena.vec_from_iter(std::iter::empty()),
            index_infos: arena.vec_from_iter(std::iter::empty()),
        }))
    }

    pub fn object_with_signatures(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
        signatures: impl IntoIterator<Item = Signature<'a>>,
    ) -> Self {
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(properties),
            signatures: arena.vec_from_iter(signatures),
            index_infos: arena.vec_from_iter(std::iter::empty()),
        }))
    }

    pub fn object_with_index_infos(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
        index_infos: impl IntoIterator<Item = IndexInfo<'a>>,
    ) -> Self {
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(properties),
            signatures: arena.vec_from_iter(std::iter::empty()),
            index_infos: arena.vec_from_iter(index_infos),
        }))
    }

    pub fn module_namespace(
        arena: CheckerArena<'a>,
        name: &'a str,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
    ) -> Self {
        Self::ModuleNamespace(arena.alloc(TyModuleNamespace {
            name,
            properties: arena.vec_from_iter(properties),
        }))
    }

    #[cfg(test)]
    pub fn function(
        arena: CheckerArena<'a>,
        type_parameters: impl IntoIterator<Item = TyTypeParameter<'a>>,
        parameters: impl IntoIterator<Item = TyParameter<'a>>,
        return_type: Ty<'a>,
    ) -> Self {
        Self::function_with_type_predicate(arena, type_parameters, parameters, return_type, None)
    }

    pub fn function_with_type_predicate(
        arena: CheckerArena<'a>,
        type_parameters: impl IntoIterator<Item = TyTypeParameter<'a>>,
        parameters: impl IntoIterator<Item = TyParameter<'a>>,
        return_type: Ty<'a>,
        type_predicate: Option<TyTypePredicate<'a>>,
    ) -> Self {
        Self::Function(arena.alloc(TyFunction {
            type_parameters: arena.vec_from_iter(type_parameters),
            parameters: arena.vec_from_iter(parameters),
            return_type,
            type_predicate: type_predicate.map(|predicate| arena.alloc(predicate)),
        }))
    }

    pub fn type_reference(
        arena: CheckerArena<'a>,
        name: &'a str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        let type_arguments = type_arguments.into_iter().collect::<Vec<_>>();
        Self::type_reference_with_explicit_type_argument_count(
            arena,
            name,
            type_arguments.iter().copied(),
            type_arguments.len(),
        )
    }

    pub fn type_reference_with_explicit_type_argument_count(
        arena: CheckerArena<'a>,
        name: &'a str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
        explicit_type_argument_count: usize,
    ) -> Self {
        let type_arguments = arena.vec_from_iter(type_arguments);
        Self::TypeReference(arena.alloc(TyTypeReference {
            name,
            explicit_type_argument_count: explicit_type_argument_count.min(type_arguments.len()),
            type_arguments,
        }))
    }

    pub fn type_query(
        arena: CheckerArena<'a>,
        name: &'a str,
        resolved: Ty<'a>,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        Self::TypeQuery(arena.alloc(TyTypeQuery {
            name,
            resolved,
            type_arguments: arena.vec_from_iter(type_arguments),
        }))
    }

    pub fn string_literal(arena: CheckerArena<'a>, value: &'a str) -> Self {
        Self::StringLiteral(arena.alloc(TyStringLiteral { value }))
    }

    pub fn array(arena: CheckerArena<'a>, element_type: Ty<'a>) -> Self {
        Self::Array(arena.alloc(TyArray {
            element_type,
            readonly: false,
        }))
    }

    pub fn readonly_array(arena: CheckerArena<'a>, element_type: Ty<'a>) -> Self {
        Self::Array(arena.alloc(TyArray {
            element_type,
            readonly: true,
        }))
    }

    pub fn tuple(arena: CheckerArena<'a>, elements: Vec<TupleElement<'a>>) -> Self {
        Self::Tuple(arena.alloc(TyTuple {
            elements: arena.vec_from_iter(elements),
            readonly: false,
        }))
    }

    pub fn readonly_tuple(arena: CheckerArena<'a>, elements: Vec<TupleElement<'a>>) -> Self {
        Self::Tuple(arena.alloc(TyTuple {
            elements: arena.vec_from_iter(elements),
            readonly: true,
        }))
    }

    pub fn r#union(arena: CheckerArena<'a>, types: impl IntoIterator<Item = Ty<'a>>) -> Self {
        reduce_union_type(arena, types)
    }

    pub fn intersection(arena: CheckerArena<'a>, types: impl IntoIterator<Item = Ty<'a>>) -> Self {
        reduce_intersection_type(arena, types)
    }

    pub fn keyof(arena: CheckerArena<'a>, target: Ty<'a>) -> Self {
        Self::Keyof(arena.alloc(TyKeyof { target }))
    }

    pub fn indexed_access(
        arena: CheckerArena<'a>,
        object_type: Ty<'a>,
        index_type: Ty<'a>,
    ) -> Self {
        Self::IndexedAccess(arena.alloc(TyIndexedAccess {
            object_type,
            index_type,
        }))
    }

    pub fn conditional(
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

    pub fn infer(arena: CheckerArena<'a>, type_parameter: TyTypeParameter<'a>) -> Self {
        Self::Infer(arena.alloc(TyInfer { type_parameter }))
    }

    pub fn mapped(
        arena: CheckerArena<'a>,
        key: &'a str,
        constraint: Ty<'a>,
        name_type: Option<Ty<'a>>,
        template: Ty<'a>,
        optional: MappedModifier,
        readonly: MappedModifier,
    ) -> Self {
        Self::Mapped(arena.alloc(TyMapped {
            key,
            constraint,
            name_type,
            template,
            optional,
            readonly,
        }))
    }

    /// Returns `true` if the type is `none`, indicating that we have no information about this type.
    /// This is normally a bug and should be investigated.
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }

    /// Returns `true` if the type is `any`.
    pub fn is_any(&self) -> bool {
        matches!(self, Self::Any)
    }

    /// Returns `true` if the type is `never`.
    pub fn is_never(&self) -> bool {
        matches!(self, Self::Never)
    }

    /// Returns `true` if the type is a numerical index type.
    pub fn is_number_index_type(&self) -> bool {
        matches!(self, Ty::Number | Ty::NumberLiteral(_))
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
            Self::Object(object) => object.properties.iter().find_map(|property| {
                (property.name == name && !property.computed).then_some(property.ty)
            }),
            Self::ModuleNamespace(namespace) => namespace.properties.iter().find_map(|property| {
                (property.name == name && !property.computed).then_some(property.ty)
            }),
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
                object.properties.iter().map(|property| TyProperty {
                    name: property.name,
                    computed: property.computed,
                    optional: property.optional,
                    method: property.method,
                    readonly: property.readonly,
                    ty: property.ty.substitute_type_parameters(arena, substitutions),
                }),
            )
            .with_index_infos(
                arena,
                object.index_infos.iter().map(|info| IndexInfo {
                    key_type: info
                        .key_type
                        .substitute_type_parameters(arena, substitutions),
                    value_type: info
                        .value_type
                        .substitute_type_parameters(arena, substitutions),
                    readonly: info.readonly,
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
                namespace.properties.iter().map(|property| TyProperty {
                    name: property.name,
                    computed: property.computed,
                    optional: property.optional,
                    method: property.method,
                    readonly: property.readonly,
                    ty: property.ty.substitute_type_parameters(arena, substitutions),
                }),
            ),
            Self::Function(function) => {
                let has_non_identity_outer_substitution = substitutions.iter().any(|(name, ty)| {
                    !function
                        .type_parameters
                        .iter()
                        .any(|type_parameter| type_parameter.name == *name)
                        && !is_identity_type_parameter_substitution(name, *ty)
                });
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
                Self::function_with_type_predicate(
                    arena,
                    function.type_parameters.iter().map(|type_parameter| {
                        Self::type_parameter_with_display_default(
                            type_parameter.name,
                            type_parameter.constraint_type.map(|constraint_type| {
                                constraint_type.substitute_type_parameters(arena, &substitutions)
                            }),
                            type_parameter.default_type.map(|default_type| {
                                default_type.substitute_type_parameters(arena, &substitutions)
                            }),
                            type_parameter.display_default && !has_non_identity_outer_substitution,
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
                    function.type_predicate.map(|predicate| {
                        predicate.substitute_type_parameters(arena, &substitutions)
                    }),
                )
            }
            Self::TypeReference(reference) => {
                if reference.type_arguments.is_empty()
                    && let Some(substitution) = substitutions.get(reference.name)
                {
                    *substitution
                } else {
                    Self::type_reference_with_explicit_type_argument_count(
                        arena,
                        reference.name,
                        reference
                            .type_arguments
                            .iter()
                            .map(|ty| ty.substitute_type_parameters(arena, substitutions)),
                        reference.explicit_type_argument_count,
                    )
                }
            }
            Self::TypeQuery(query) => Self::type_query(
                arena,
                query.name,
                query
                    .resolved
                    .substitute_type_parameters(arena, substitutions),
                query
                    .type_arguments
                    .iter()
                    .map(|ty| ty.substitute_type_parameters(arena, substitutions)),
            ),
            Self::Array(array) => Self::Array(
                arena.alloc(TyArray {
                    element_type: array
                        .element_type
                        .substitute_type_parameters(arena, substitutions),
                    readonly: array.readonly,
                }),
            ),
            Self::Tuple(tuple) => Self::Tuple(arena.alloc(TyTuple {
                elements: arena.vec_from_iter(tuple.elements.iter().map(|element| match element {
                    TupleElement::Regular(ty) => {
                        TupleElement::Regular(ty.substitute_type_parameters(arena, substitutions))
                    }
                    TupleElement::Rest(ty) => {
                        TupleElement::Rest(ty.substitute_type_parameters(arena, substitutions))
                    }
                    TupleElement::Optional(ty) => {
                        TupleElement::Optional(ty.substitute_type_parameters(arena, substitutions))
                    }
                })),
                readonly: tuple.readonly,
            })),
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
                let infer_type_parameters = infer_type_parameter_names(conditional.extends_type);
                let infer_substitutions = substitutions_without_names(
                    substitutions,
                    infer_type_parameters.iter().copied(),
                );

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
                            let infer_substitutions = substitutions_without_names(
                                &substitutions,
                                infer_type_parameters.iter().copied(),
                            );
                            Self::conditional(
                                arena,
                                *ty,
                                conditional
                                    .extends_type
                                    .substitute_type_parameters(arena, &infer_substitutions),
                                conditional
                                    .true_type
                                    .substitute_type_parameters(arena, &infer_substitutions),
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
                        .substitute_type_parameters(arena, &infer_substitutions),
                    conditional
                        .true_type
                        .substitute_type_parameters(arena, &infer_substitutions),
                    conditional
                        .false_type
                        .substitute_type_parameters(arena, substitutions),
                    conditional.is_distributive,
                )
            }
            Self::Infer(infer) => {
                let substitutions = substitutions_without_names(
                    substitutions,
                    std::iter::once(infer.type_parameter.name),
                );
                Self::infer(
                    arena,
                    Self::type_parameter_with_display_default(
                        infer.type_parameter.name,
                        infer.type_parameter.constraint_type.map(|constraint_type| {
                            constraint_type.substitute_type_parameters(arena, &substitutions)
                        }),
                        infer.type_parameter.default_type.map(|default_type| {
                            default_type.substitute_type_parameters(arena, &substitutions)
                        }),
                        infer.type_parameter.display_default,
                    ),
                )
            }
            Self::Mapped(mapped) => {
                // TODO(correctness): The mapped key `P` shadows outer type parameters; this
                // does not currently scrub it from `substitutions` when recursing.
                Self::mapped(
                    arena,
                    mapped.key,
                    mapped
                        .constraint
                        .substitute_type_parameters(arena, substitutions),
                    mapped
                        .name_type
                        .map(|ty| ty.substitute_type_parameters(arena, substitutions)),
                    mapped
                        .template
                        .substitute_type_parameters(arena, substitutions),
                    mapped.optional,
                    mapped.readonly,
                )
            }
            _ => *self,
        }
    }

    pub fn enum_variant_name(self) -> &'static str {
        match self {
            Self::None => "TyNone",
            Self::Number => "TyNumber",
            Self::String => "TyString",
            Self::Boolean => "TyBoolean",
            Self::Bigint => "TyBigint",
            Self::Symbol => "TySymbol",
            Self::UniqueSymbol(_) => "TyUniqueSymbol",
            Self::Undefined => "TyUndefined",
            Self::Null => "TyNull",
            Self::Any => "TyAny",
            Self::Unknown => "TyUnknown",
            Self::Void => "TyVoid",
            Self::Never => "TyNever",
            Self::Object(_) => "TyObject",
            Self::ModuleNamespace(_) => "TyModuleNamespace",
            Self::PrimitiveObject => "TyPrimitiveObject",
            Self::This => "TyThis",
            Self::Function(_) => "TyFunction",
            Self::TypeReference(_) => "TyTypeReference",
            Self::TypeQuery(_) => "TyTypeQuery",
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
            Self::Mapped(_) => "TyMapped",
        }
    }

    #[allow(dead_code)]
    pub(crate) fn to_type_string(self) -> String {
        match self {
            Self::None => "none".to_string(),
            Self::Number => "number".to_string(),
            Self::String => "string".to_string(),
            Self::Boolean => "boolean".to_string(),
            Self::Bigint => "bigint".to_string(),
            Self::Symbol => "symbol".to_string(),
            Self::UniqueSymbol(unique_symbol) => unique_symbol.name.map_or_else(
                || "unique symbol".to_string(),
                |name| format!("typeof {name}"),
            ),
            Self::Undefined => "undefined".to_string(),
            Self::Null => "null".to_string(),
            Self::Any => "any".to_string(),
            Self::Unknown => "unknown".to_string(),
            Self::Void => "void".to_string(),
            Self::Never => "never".to_string(),
            Self::PrimitiveObject => "object".to_string(),
            Self::This => "this".to_string(),
            Self::Object(object) => {
                if object.properties.is_empty()
                    && object.signatures.is_empty()
                    && object.index_infos.is_empty()
                {
                    return "{}".to_string();
                }

                let members = object
                    .signatures
                    .iter()
                    .map(|signature| signature.to_type_string())
                    .chain(object.index_infos.iter().map(|info| {
                        let readonly = if info.readonly { "readonly " } else { "" };
                        format!(
                            "{}[x: {}]: {};",
                            readonly,
                            info.key_type.to_type_string(),
                            info.value_type.to_type_string()
                        )
                    }))
                    .chain(object.properties.iter().map(|property| {
                        let readonly = if property.readonly { "readonly " } else { "" };
                        if property.method
                            && let Ty::Function(function) = property.ty
                        {
                            format!(
                                "{}{}{};",
                                readonly,
                                property_name_to_type_string(property),
                                signature_to_type_string(function)
                            )
                        } else {
                            format!(
                                "{}{}: {};",
                                readonly,
                                property_name_to_type_string(property),
                                property.ty.to_type_string()
                            )
                        }
                    }))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("{{ {members} }}")
            }
            Self::ModuleNamespace(namespace) => format!("typeof {}", namespace.name),
            Self::Function(function) => function_type_to_string(function),
            Self::TypeReference(reference) => {
                if reference.explicit_type_argument_count == 0 {
                    reference.name.to_string()
                } else {
                    let type_arguments = reference
                        .type_arguments
                        .iter()
                        .take(reference.explicit_type_argument_count)
                        .map(|ty| ty.to_type_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{type_arguments}>", reference.name)
                }
            }
            Self::TypeQuery(query) => {
                if query.type_arguments.is_empty() {
                    format!("typeof {}", query.name)
                } else {
                    let type_arguments = query
                        .type_arguments
                        .iter()
                        .map(|ty| ty.to_type_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("typeof {}<{type_arguments}>", query.name)
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
            Self::BooleanLiteral(value) => value.to_string(),
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
                let body = if array.element_type.display_needs_parentheses() {
                    format!("({element_type})[]")
                } else {
                    format!("{element_type}[]")
                };
                if array.readonly {
                    format!("readonly {body}")
                } else {
                    body
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
                if tuple.readonly {
                    format!("readonly [{elements}]")
                } else {
                    format!("[{elements}]")
                }
            }
            Self::Union(union) => union
                .types
                .iter()
                .map(|ty| {
                    let type_string = ty.to_type_string();
                    if ty.display_needs_parentheses() {
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
                    if ty.display_needs_parentheses() {
                        format!("({type_string})")
                    } else {
                        type_string
                    }
                })
                .collect::<Vec<_>>()
                .join(" & "),
            Self::Keyof(keyof) => {
                let target = keyof.target.to_type_string();
                if keyof.target.display_needs_parentheses() {
                    format!("keyof ({target})")
                } else {
                    format!("keyof {target}")
                }
            }
            Self::IndexedAccess(indexed_access) => {
                let object_type = indexed_access.object_type.to_type_string();
                let index_type = indexed_access.index_type.to_type_string();
                if indexed_access.object_type.display_needs_parentheses() {
                    format!("({object_type})[{index_type}]")
                } else {
                    format!("{object_type}[{index_type}]")
                }
            }
            Self::Conditional(conditional) => {
                let check_type = conditional.check_type.to_type_string();
                let extends_type = conditional.extends_type.to_type_string();
                let check_type = if conditional.check_type.display_needs_parentheses() {
                    format!("({check_type})")
                } else {
                    check_type
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
            Self::Mapped(mapped) => {
                let mut s = String::from("{ ");
                s.push_str(mapped_modifier_prefix(mapped.readonly, "readonly "));
                s.push('[');
                s.push_str(mapped.key);
                s.push_str(" in ");
                s.push_str(&mapped.constraint.to_type_string());
                if let Some(name_type) = mapped.name_type {
                    s.push_str(" as ");
                    s.push_str(&name_type.to_type_string());
                }
                s.push(']');
                s.push_str(mapped_modifier_suffix(mapped.optional, "?"));
                s.push_str(": ");
                s.push_str(&mapped.template.to_type_string());
                s.push_str("; }");
                s
            }
        }
    }

    /// Whether this type needs parentheses when printed
    fn display_needs_parentheses(&self) -> bool {
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
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(object.properties.iter().copied()),
            signatures: arena.vec_from_iter(signatures),
            index_infos: arena.vec_from_iter(object.index_infos.iter().copied()),
        }))
    }

    fn with_index_infos(
        self,
        arena: CheckerArena<'a>,
        index_infos: impl IntoIterator<Item = IndexInfo<'a>>,
    ) -> Self {
        let Self::Object(object) = self else {
            return self;
        };
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(object.properties.iter().copied()),
            signatures: arena.vec_from_iter(object.signatures.iter().copied()),
            index_infos: arena.vec_from_iter(index_infos),
        }))
    }

    /// Returns `true` if the type is [`Ty::Object`] with no properties, no signatures, and has index infos.
    pub fn is_index_signature_object(&self) -> bool {
        let Ty::Object(object) = self else {
            return false;
        };
        object.signatures.is_empty()
            && object.properties.is_empty()
            && !object.index_infos.is_empty()
    }

    /// Returns the element type of an array type, or `None` if the type is not an array.
    pub fn array_element_type(&self) -> Option<Self> {
        let Ty::Array(array) = self else {
            return None;
        };
        Some(array.element_type)
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
    if let Some(is_equal) = simplify_type_equality_function_extends(check_type, extends_type) {
        return if is_equal { true_type } else { false_type };
    }

    if contains_infer(check_type) || contains_infer(extends_type) {
        let mut inferences = InferInferences::new(arena);
        return match infer_from_types(arena, check_type, extends_type, &mut inferences, 0) {
            InferMatchResult::Matched => {
                true_type.substitute_type_parameters(arena, &inferences.substitutions)
            }
            InferMatchResult::NoMatch => false_type,
            InferMatchResult::Deferred => Ty::Conditional(arena.alloc(TyConditional {
                check_type,
                extends_type,
                true_type,
                false_type,
                is_distributive,
            })),
        };
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

fn simplify_type_equality_function_extends(
    check_type: Ty<'_>,
    extends_type: Ty<'_>,
) -> Option<bool> {
    let (Ty::Function(check_function), Ty::Function(extends_function)) = (check_type, extends_type)
    else {
        return None;
    };
    if !check_function.parameters.is_empty()
        || !extends_function.parameters.is_empty()
        || check_function.type_parameters.len() != 1
        || extends_function.type_parameters.len() != 1
    {
        return None;
    }

    let Ty::Conditional(check_return) = check_function.return_type else {
        return None;
    };
    let Ty::Conditional(extends_return) = extends_function.return_type else {
        return None;
    };
    if !is_conditional_equality_probe(check_return, check_function.type_parameters[0].name)
        || !is_conditional_equality_probe(extends_return, extends_function.type_parameters[0].name)
    {
        return None;
    }
    if contains_unresolved_type_variable(check_return.extends_type)
        || contains_unresolved_type_variable(extends_return.extends_type)
    {
        return None;
    }

    Some(
        crate::relations::is_assignable_to(check_return.extends_type, extends_return.extends_type)
            && crate::relations::is_assignable_to(
                extends_return.extends_type,
                check_return.extends_type,
            ),
    )
}

fn is_conditional_equality_probe(
    conditional: &TyConditional<'_>,
    type_parameter_name: &str,
) -> bool {
    matches!(conditional.check_type, Ty::TypeReference(reference) if reference.name == type_parameter_name && reference.type_arguments.is_empty())
        && matches!(conditional.true_type, Ty::NumberLiteral(literal) if literal.value == "1")
        && matches!(conditional.false_type, Ty::NumberLiteral(literal) if literal.value == "0")
}
const INFER_MATCH_MAX_DEPTH: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InferMatchResult {
    Matched,
    NoMatch,
    Deferred,
}

impl InferMatchResult {
    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::NoMatch, _) | (_, Self::NoMatch) => Self::NoMatch,
            (Self::Deferred, _) | (_, Self::Deferred) => Self::Deferred,
            (Self::Matched, Self::Matched) => Self::Matched,
        }
    }
}

#[derive(Clone)]
struct InferInferences<'a> {
    arena: CheckerArena<'a>,
    substitutions: HashMap<&'a str, Ty<'a>>,
}

impl<'a> InferInferences<'a> {
    fn new(arena: CheckerArena<'a>) -> Self {
        Self {
            arena,
            substitutions: HashMap::new(),
        }
    }

    fn add(&mut self, infer: &TyInfer<'a>, candidate: Ty<'a>) -> InferMatchResult {
        if let Some(constraint_type) = infer.type_parameter.constraint_type {
            let constraint_type =
                constraint_type.substitute_type_parameters(self.arena, &self.substitutions);
            if contains_infer(constraint_type) || contains_unresolved_type_variable(constraint_type)
            {
                return InferMatchResult::Deferred;
            }
            if !crate::relations::is_assignable_to(candidate, constraint_type) {
                return InferMatchResult::NoMatch;
            }
        }

        match self.substitutions.get(infer.type_parameter.name).copied() {
            Some(existing) if existing == candidate => InferMatchResult::Matched,
            Some(existing) => {
                let candidate = Ty::r#union(self.arena, [existing, candidate]);
                self.substitutions
                    .insert(infer.type_parameter.name, candidate);
                InferMatchResult::Matched
            }
            None => {
                self.substitutions
                    .insert(infer.type_parameter.name, candidate);
                InferMatchResult::Matched
            }
        }
    }
}

fn infer_from_types<'a>(
    arena: CheckerArena<'a>,
    source: Ty<'a>,
    target: Ty<'a>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    if depth >= INFER_MATCH_MAX_DEPTH {
        return InferMatchResult::Deferred;
    }

    if source == target && !contains_infer(target) {
        return InferMatchResult::Matched;
    }

    match (source, target) {
        (_, Ty::Infer(infer)) => inferences.add(infer, source),
        (Ty::Any, target) if contains_infer(target) => infer_any_to_type(target, inferences),
        (Ty::Object(source), Ty::Object(target)) => infer_from_properties(
            arena,
            source.properties.iter().copied(),
            target.properties.iter().copied(),
            inferences,
            depth + 1,
        )
        .and(infer_from_signatures(
            arena,
            source.signatures.iter().copied(),
            target.signatures.iter().copied(),
            inferences,
            depth + 1,
        )),
        (Ty::ModuleNamespace(source), Ty::Object(target)) => infer_from_properties(
            arena,
            source.properties.iter().copied(),
            target.properties.iter().copied(),
            inferences,
            depth + 1,
        ),
        (Ty::Object(source), Ty::ModuleNamespace(target)) => infer_from_properties(
            arena,
            source.properties.iter().copied(),
            target.properties.iter().copied(),
            inferences,
            depth + 1,
        ),
        (Ty::ModuleNamespace(source), Ty::ModuleNamespace(target)) => infer_from_properties(
            arena,
            source.properties.iter().copied(),
            target.properties.iter().copied(),
            inferences,
            depth + 1,
        ),
        (Ty::Function(source), Ty::Function(target)) => {
            infer_from_functions(arena, source, target, inferences, depth + 1)
        }
        (Ty::TypeReference(source), Ty::TypeReference(target)) => {
            if source.name != target.name
                || source.type_arguments.len() != target.type_arguments.len()
            {
                return if contains_unresolved_type_variable(Ty::TypeReference(source)) {
                    InferMatchResult::Deferred
                } else {
                    InferMatchResult::NoMatch
                };
            }
            infer_from_type_iter(
                arena,
                source.type_arguments.iter().copied(),
                target.type_arguments.iter().copied(),
                inferences,
                depth + 1,
            )
        }
        (Ty::TypeReference(_), target) if contains_infer(target) => InferMatchResult::Deferred,
        (Ty::TypeQuery(source), Ty::TypeQuery(target)) => {
            if source.name != target.name
                || source.type_arguments.len() != target.type_arguments.len()
            {
                return InferMatchResult::NoMatch;
            }
            infer_from_types(
                arena,
                source.resolved,
                target.resolved,
                inferences,
                depth + 1,
            )
            .and(infer_from_type_iter(
                arena,
                source.type_arguments.iter().copied(),
                target.type_arguments.iter().copied(),
                inferences,
                depth + 1,
            ))
        }
        (Ty::TypeQuery(source), target) => {
            infer_from_types(arena, source.resolved, target, inferences, depth + 1)
        }
        (source, Ty::TypeQuery(target)) => {
            infer_from_types(arena, source, target.resolved, inferences, depth + 1)
        }
        (Ty::Array(source), Ty::Array(target)) => infer_from_types(
            arena,
            source.element_type,
            target.element_type,
            inferences,
            depth + 1,
        ),
        (Ty::Tuple(source), Ty::Tuple(target)) => infer_from_tuple_elements(
            arena,
            &source.elements,
            &target.elements,
            inferences,
            depth + 1,
        ),
        (Ty::Union(source), Ty::Union(target)) if source.types.len() == target.types.len() => {
            infer_from_type_iter(
                arena,
                source.types.iter().copied(),
                target.types.iter().copied(),
                inferences,
                depth + 1,
            )
        }
        (Ty::Union(source), target) => infer_from_source_union(
            arena,
            source.types.iter().copied(),
            target,
            inferences,
            depth + 1,
        ),
        (source, Ty::Union(target)) => infer_from_target_union(
            arena,
            source,
            target.types.iter().copied(),
            inferences,
            depth + 1,
        ),
        (Ty::Intersection(source), Ty::Intersection(target))
            if source.types.len() == target.types.len() =>
        {
            infer_from_type_iter(
                arena,
                source.types.iter().copied(),
                target.types.iter().copied(),
                inferences,
                depth + 1,
            )
        }
        (Ty::Intersection(source), Ty::Object(target)) => infer_from_intersection_properties(
            arena,
            source.types.iter().copied(),
            target.properties.iter().copied(),
            inferences,
            depth + 1,
        ),
        (Ty::Keyof(source), Ty::Keyof(target)) => {
            infer_from_types(arena, source.target, target.target, inferences, depth + 1)
        }
        (Ty::IndexedAccess(source), Ty::IndexedAccess(target)) => infer_from_types(
            arena,
            source.object_type,
            target.object_type,
            inferences,
            depth + 1,
        )
        .and(infer_from_types(
            arena,
            source.index_type,
            target.index_type,
            inferences,
            depth + 1,
        )),
        (Ty::Conditional(source), Ty::Conditional(target)) => infer_from_types(
            arena,
            source.check_type,
            target.check_type,
            inferences,
            depth + 1,
        )
        .and(infer_from_types(
            arena,
            source.extends_type,
            target.extends_type,
            inferences,
            depth + 1,
        ))
        .and(infer_from_types(
            arena,
            source.true_type,
            target.true_type,
            inferences,
            depth + 1,
        ))
        .and(infer_from_types(
            arena,
            source.false_type,
            target.false_type,
            inferences,
            depth + 1,
        )),
        (Ty::Mapped(_), Ty::Mapped(_)) if contains_infer(target) => InferMatchResult::Deferred,
        _ => {
            if crate::relations::is_assignable_to(source, target) {
                InferMatchResult::Matched
            } else if contains_unresolved_type_variable(source)
                || contains_unresolved_type_variable(target)
            {
                InferMatchResult::Deferred
            } else {
                InferMatchResult::NoMatch
            }
        }
    }
}

fn infer_any_to_type<'a>(target: Ty<'a>, inferences: &mut InferInferences<'a>) -> InferMatchResult {
    let mut result = InferMatchResult::Matched;
    collect_infer_types(target, &mut |infer| {
        result = result.and(inferences.add(infer, Ty::any()));
    });
    result
}

fn infer_from_properties<'a>(
    arena: CheckerArena<'a>,
    source_properties: impl IntoIterator<Item = TyProperty<'a>>,
    target_properties: impl IntoIterator<Item = TyProperty<'a>>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    let source_properties = source_properties.into_iter().collect::<Vec<_>>();
    let mut result = InferMatchResult::Matched;

    for target_property in target_properties {
        let Some(source_property) = source_properties.iter().find(|source_property| {
            source_property.name == target_property.name
                && source_property.computed == target_property.computed
        }) else {
            if target_property.optional {
                continue;
            }
            return InferMatchResult::NoMatch;
        };

        if source_property.optional && !target_property.optional {
            return InferMatchResult::NoMatch;
        }

        result = result.and(infer_from_types(
            arena,
            source_property.ty,
            target_property.ty,
            inferences,
            depth + 1,
        ));
        if result == InferMatchResult::NoMatch {
            return result;
        }
    }

    result
}

fn infer_from_intersection_properties<'a>(
    arena: CheckerArena<'a>,
    source_types: impl IntoIterator<Item = Ty<'a>>,
    target_properties: impl IntoIterator<Item = TyProperty<'a>>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    let source_properties = source_types
        .into_iter()
        .flat_map(intersection_infer_properties)
        .collect::<Vec<_>>();
    infer_from_properties(
        arena,
        source_properties,
        target_properties,
        inferences,
        depth + 1,
    )
}

fn intersection_infer_properties(ty: Ty<'_>) -> Vec<TyProperty<'_>> {
    match ty {
        Ty::Object(object) => object.properties.iter().copied().collect(),
        Ty::ModuleNamespace(namespace) => namespace.properties.iter().copied().collect(),
        Ty::Intersection(intersection) => intersection
            .types
            .iter()
            .flat_map(|ty| intersection_infer_properties(*ty))
            .collect(),
        _ => Vec::new(),
    }
}

fn infer_from_signatures<'a>(
    arena: CheckerArena<'a>,
    source_signatures: impl IntoIterator<Item = Signature<'a>>,
    target_signatures: impl IntoIterator<Item = Signature<'a>>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    let source_signatures = source_signatures.into_iter().collect::<Vec<_>>();
    let mut result = InferMatchResult::Matched;

    for target_signature in target_signatures {
        let Some(source_signature) = source_signatures
            .iter()
            .find(|source_signature| source_signature.kind == target_signature.kind)
        else {
            return InferMatchResult::NoMatch;
        };
        result = result.and(infer_from_functions(
            arena,
            source_signature.function,
            target_signature.function,
            inferences,
            depth + 1,
        ));
    }

    result
}

fn infer_from_functions<'a>(
    arena: CheckerArena<'a>,
    source: &TyFunction<'a>,
    target: &TyFunction<'a>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    if source.parameters.len() != target.parameters.len() {
        return InferMatchResult::NoMatch;
    }

    let parameters = source
        .parameters
        .iter()
        .zip(target.parameters.iter())
        .map(|(source_parameter, target_parameter)| (source_parameter.ty, target_parameter.ty));
    let return_type_result = match target.type_predicate {
        Some(target_predicate) => {
            let Some(source_predicate) = source.type_predicate else {
                return InferMatchResult::NoMatch;
            };
            if !type_predicate_kinds_match(source_predicate, target_predicate) {
                return InferMatchResult::NoMatch;
            }
            match (source_predicate.target_type, target_predicate.target_type) {
                (Some(source_type), Some(target_type)) => {
                    infer_from_types(arena, source_type, target_type, inferences, depth + 1)
                }
                (None, None) => InferMatchResult::Matched,
                _ => InferMatchResult::NoMatch,
            }
        }
        None => infer_from_types(
            arena,
            source.return_type,
            target.return_type,
            inferences,
            depth + 1,
        ),
    };
    infer_from_type_pairs(arena, parameters, inferences, depth + 1).and(return_type_result)
}

fn infer_from_tuple_elements<'a>(
    arena: CheckerArena<'a>,
    source_elements: &ArenaVec<'a, TupleElement<'a>>,
    target_elements: &ArenaVec<'a, TupleElement<'a>>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    if let Some((rest_index, TupleElement::Rest(rest_type))) = target_elements
        .iter()
        .enumerate()
        .find(|(_, element)| matches!(element, TupleElement::Rest(_)))
    {
        if rest_index + 1 != target_elements.len() || source_elements.len() < rest_index {
            return InferMatchResult::Deferred;
        }
        let mut result = infer_from_tuple_elements(
            arena,
            &arena.vec_from_iter(source_elements.iter().take(rest_index).copied()),
            &arena.vec_from_iter(target_elements.iter().take(rest_index).copied()),
            inferences,
            depth + 1,
        );
        let rest_tuple = Ty::tuple(
            arena,
            source_elements
                .iter()
                .skip(rest_index)
                .copied()
                .collect::<Vec<_>>(),
        );
        result = result.and(infer_from_types(
            arena,
            rest_tuple,
            *rest_type,
            inferences,
            depth + 1,
        ));
        return result;
    }

    if source_elements.len() != target_elements.len() {
        return InferMatchResult::NoMatch;
    }

    let element_pairs = source_elements
        .iter()
        .zip(target_elements.iter())
        .map(|(source, target)| (tuple_element_type(*source), tuple_element_type(*target)));
    infer_from_type_pairs(arena, element_pairs, inferences, depth + 1)
}

fn infer_from_source_union<'a>(
    arena: CheckerArena<'a>,
    source_types: impl IntoIterator<Item = Ty<'a>>,
    target: Ty<'a>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    let mut result = InferMatchResult::Matched;
    for source_type in source_types {
        result = result.and(infer_from_types(
            arena,
            source_type,
            target,
            inferences,
            depth + 1,
        ));
        if result == InferMatchResult::NoMatch {
            return result;
        }
    }
    result
}

fn infer_from_target_union<'a>(
    arena: CheckerArena<'a>,
    source: Ty<'a>,
    target_types: impl IntoIterator<Item = Ty<'a>>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    let mut deferred = false;
    for target_type in target_types {
        let mut branch_inferences = inferences.clone();
        match infer_from_types(
            arena,
            source,
            target_type,
            &mut branch_inferences,
            depth + 1,
        ) {
            InferMatchResult::Matched => {
                *inferences = branch_inferences;
                return InferMatchResult::Matched;
            }
            InferMatchResult::Deferred => deferred = true,
            InferMatchResult::NoMatch => {}
        }
    }

    if deferred {
        InferMatchResult::Deferred
    } else {
        InferMatchResult::NoMatch
    }
}

fn infer_from_type_iter<'a>(
    arena: CheckerArena<'a>,
    source: impl IntoIterator<Item = Ty<'a>>,
    target: impl IntoIterator<Item = Ty<'a>>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    infer_from_type_pairs(arena, source.into_iter().zip(target), inferences, depth)
}

fn infer_from_type_pairs<'a>(
    arena: CheckerArena<'a>,
    pairs: impl IntoIterator<Item = (Ty<'a>, Ty<'a>)>,
    inferences: &mut InferInferences<'a>,
    depth: usize,
) -> InferMatchResult {
    pairs
        .into_iter()
        .fold(InferMatchResult::Matched, |result, (source, target)| {
            result.and(infer_from_types(
                arena,
                source,
                target,
                inferences,
                depth + 1,
            ))
        })
}

fn tuple_element_type(element: TupleElement<'_>) -> Ty<'_> {
    match element {
        TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => ty,
    }
}

fn infer_type_parameter_names<'a>(ty: Ty<'a>) -> Vec<&'a str> {
    let mut names = Vec::new();
    collect_infer_types(ty, &mut |infer| {
        if !names.contains(&infer.type_parameter.name) {
            names.push(infer.type_parameter.name);
        }
    });
    names
}

fn collect_infer_types<'a>(ty: Ty<'a>, f: &mut impl FnMut(&TyInfer<'a>)) {
    match ty {
        Ty::Infer(infer) => f(infer),
        Ty::Object(object) => {
            for property in &object.properties {
                collect_infer_types(property.ty, f);
            }
            for signature in &object.signatures {
                collect_infer_types(Ty::Function(signature.function), f);
            }
        }
        Ty::ModuleNamespace(namespace) => {
            for property in &namespace.properties {
                collect_infer_types(property.ty, f);
            }
        }
        Ty::Function(function) => {
            for type_parameter in &function.type_parameters {
                if let Some(constraint_type) = type_parameter.constraint_type {
                    collect_infer_types(constraint_type, f);
                }
                if let Some(default_type) = type_parameter.default_type {
                    collect_infer_types(default_type, f);
                }
            }
            for parameter in &function.parameters {
                collect_infer_types(parameter.ty, f);
            }
            collect_infer_types(function.return_type, f);
            if let Some(target_type) = function
                .type_predicate
                .and_then(|predicate| predicate.target_type)
            {
                collect_infer_types(target_type, f);
            }
        }
        Ty::TypeReference(reference) => {
            for ty in &reference.type_arguments {
                collect_infer_types(*ty, f);
            }
        }
        Ty::TypeQuery(query) => {
            collect_infer_types(query.resolved, f);
            for ty in &query.type_arguments {
                collect_infer_types(*ty, f);
            }
        }
        Ty::TemplateLiteral(template_literal) => {
            for ty in &template_literal.expressions {
                collect_infer_types(*ty, f);
            }
        }
        Ty::Array(array) => collect_infer_types(array.element_type, f),
        Ty::Tuple(tuple) => {
            for element in &tuple.elements {
                collect_infer_types(tuple_element_type(*element), f);
            }
        }
        Ty::Union(union) => {
            for ty in &union.types {
                collect_infer_types(*ty, f);
            }
        }
        Ty::Intersection(intersection) => {
            for ty in &intersection.types {
                collect_infer_types(*ty, f);
            }
        }
        Ty::Keyof(keyof) => collect_infer_types(keyof.target, f),
        Ty::IndexedAccess(indexed_access) => {
            collect_infer_types(indexed_access.object_type, f);
            collect_infer_types(indexed_access.index_type, f);
        }
        Ty::Conditional(conditional) => {
            collect_infer_types(conditional.check_type, f);
            collect_infer_types(conditional.extends_type, f);
            collect_infer_types(conditional.true_type, f);
            collect_infer_types(conditional.false_type, f);
        }
        Ty::Mapped(mapped) => {
            collect_infer_types(mapped.constraint, f);
            if let Some(name_type) = mapped.name_type {
                collect_infer_types(name_type, f);
            }
            collect_infer_types(mapped.template, f);
        }
        _ => {}
    }
}

fn substitutions_without_names<'a>(
    substitutions: &HashMap<&'a str, Ty<'a>>,
    names: impl IntoIterator<Item = &'a str>,
) -> HashMap<&'a str, Ty<'a>> {
    let names = names.into_iter().collect::<Vec<_>>();
    substitutions
        .iter()
        .filter(|(name, _)| !names.contains(name))
        .map(|(name, ty)| (*name, *ty))
        .collect()
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
                || function
                    .type_predicate
                    .and_then(|predicate| predicate.target_type)
                    .is_some_and(contains_unresolved_type_variable)
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
        Ty::Mapped(mapped) => {
            contains_unresolved_type_variable(mapped.constraint)
                || mapped
                    .name_type
                    .is_some_and(contains_unresolved_type_variable)
                || contains_unresolved_type_variable(mapped.template)
        }
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
                || function
                    .type_predicate
                    .and_then(|predicate| predicate.target_type)
                    .is_some_and(contains_infer)
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
        Ty::Mapped(mapped) => {
            contains_infer(mapped.constraint)
                || mapped.name_type.is_some_and(contains_infer)
                || contains_infer(mapped.template)
        }
        _ => false,
    }
}

fn is_identity_type_parameter_substitution(name: &str, ty: Ty<'_>) -> bool {
    matches!(ty, Ty::TypeReference(reference) if reference.name == name && reference.type_arguments.is_empty())
}

fn reduce_intersection_type<'a>(
    arena: CheckerArena<'a>,
    types: impl IntoIterator<Item = Ty<'a>>,
) -> Ty<'a> {
    let mut type_set = Vec::new();
    for ty in types {
        add_type_to_intersection(&mut type_set, ty);
    }

    if type_set.len() > 1 {
        type_set.retain(|ty| !matches!(ty, Ty::Unknown));
    }

    let has_object_like_member = type_set
        .iter()
        .any(|ty| is_empty_object_intersection_identity_target(*ty));
    if has_object_like_member {
        type_set.retain(|ty| !matches!(ty, Ty::Object(object) if object.is_empty()));
    }

    match type_set.as_slice() {
        [] => Ty::object(arena, []),
        [ty] => *ty,
        _ => Ty::Intersection(arena.alloc(TyIntersection {
            types: arena.vec_from_iter(type_set),
        })),
    }
}

fn add_type_to_intersection<'a>(type_set: &mut Vec<Ty<'a>>, ty: Ty<'a>) {
    if let Ty::Intersection(intersection) = ty {
        for ty in &intersection.types {
            add_type_to_intersection(type_set, *ty);
        }
    } else if !type_set.contains(&ty) {
        type_set.push(ty);
    }
}

fn is_empty_object_intersection_identity_target(ty: Ty<'_>) -> bool {
    match ty {
        Ty::Mapped(_) => true,
        Ty::Object(object) => !object.is_empty(),
        _ => false,
    }
}

fn element_type_needs_parentheses(element: &TupleElement<'_>) -> bool {
    match element {
        TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => {
            ty.display_needs_parentheses()
        }
    }
}

/// Render the `+`/`-`/none polarity for a mapped readonly-style modifier, with a trailing space.
fn mapped_modifier_prefix(modifier: MappedModifier, keyword: &'static str) -> &'static str {
    match (modifier, keyword) {
        (MappedModifier::None, _) => "",
        (MappedModifier::True, "readonly ") => "readonly ",
        (MappedModifier::Plus, "readonly ") => "+readonly ",
        (MappedModifier::Minus, "readonly ") => "-readonly ",
        // Only `readonly` is rendered as a prefix today.
        _ => "",
    }
}

/// Render the `+`/`-`/none polarity for a mapped optional-style modifier suffix.
fn mapped_modifier_suffix(modifier: MappedModifier, keyword: &'static str) -> &'static str {
    match (modifier, keyword) {
        (MappedModifier::None, _) => "",
        (MappedModifier::True, "?") => "?",
        (MappedModifier::Plus, "?") => "+?",
        (MappedModifier::Minus, "?") => "-?",
        _ => "",
    }
}

fn type_parameter_to_type_string(type_parameter: &TyTypeParameter<'_>) -> String {
    let mut type_string = type_parameter.name.to_string();
    if let Some(constraint_type) = type_parameter.constraint_type {
        type_string.push_str(" extends ");
        type_string.push_str(&constraint_type.to_type_string());
    }
    if type_parameter.display_default
        && let Some(default_type) = type_parameter.default_type
    {
        type_string.push_str(" = ");
        type_string.push_str(&default_type.to_type_string());
    }
    type_string
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SignatureKind {
    Call,
    Construct,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Signature<'a> {
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct IndexInfo<'a> {
    /// The type of the index key. The `K` in `{ [k: K]: V }` or `string` in `{ [k: string]: number }`
    pub(crate) key_type: Ty<'a>,
    /// The type of the index value. The `V` in `{ [k: K]: V }` or `string` in `{ [k: string]: number }`
    pub(crate) value_type: Ty<'a>,
    /// Whether the index returns a readonly value.
    pub(crate) readonly: bool,
}

fn function_type_to_string(function: &TyFunction<'_>) -> String {
    let (type_parameters, parameters) = function_type_head_to_string(function);
    format!(
        "{type_parameters}({parameters}) => {}",
        function_return_type_to_string(function)
    )
}

fn signature_to_type_string(function: &TyFunction<'_>) -> String {
    let (type_parameters, parameters) = function_type_head_to_string(function);
    format!(
        "{type_parameters}({parameters}): {}",
        function_return_type_to_string(function)
    )
}

fn function_return_type_to_string(function: &TyFunction<'_>) -> String {
    function.type_predicate.map_or_else(
        || function.return_type.to_type_string(),
        type_predicate_to_type_string,
    )
}

fn type_predicate_to_type_string(predicate: &TyTypePredicate<'_>) -> String {
    let parameter_name = predicate.parameter_name.unwrap_or("this");
    let mut type_string = String::new();
    if predicate.kind.is_asserts() {
        type_string.push_str("asserts ");
    }
    type_string.push_str(parameter_name);
    if let Some(target_type) = predicate.target_type {
        type_string.push_str(" is ");
        type_string.push_str(&target_type.to_type_string());
    }
    type_string
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

pub(crate) fn return_type_and_type_predicate_from_annotation_with_resolver<'a>(
    parameters: &[TyParameter<'a>],
    return_type: Option<&TSTypeAnnotation<'a>>,
    resolve_type_annotation: impl Fn(&TSTypeAnnotation<'a>) -> Ty<'a>,
) -> (Ty<'a>, Option<TyTypePredicate<'a>>) {
    let Some(return_type) = return_type else {
        return (Ty::any(), None);
    };
    let TSType::TSTypePredicate(predicate) = &return_type.type_annotation else {
        return (resolve_type_annotation(return_type), None);
    };
    let target_type = predicate
        .type_annotation
        .as_deref()
        .map(resolve_type_annotation);
    (
        type_predicate_return_type(predicate.asserts),
        Some(type_predicate_from_ts_type_predicate_with_target_type(
            parameters,
            predicate,
            target_type,
        )),
    )
}

pub(crate) fn type_predicate_return_type<'a>(asserts: bool) -> Ty<'a> {
    if asserts { Ty::void() } else { Ty::boolean() }
}

pub(crate) fn type_predicate_from_ts_type_predicate_with_target_type<'a>(
    parameters: &[TyParameter<'a>],
    predicate: &TSTypePredicate<'a>,
    target_type: Option<Ty<'a>>,
) -> TyTypePredicate<'a> {
    match &predicate.parameter_name {
        TSTypePredicateName::Identifier(identifier) => {
            let parameter_name = identifier.name.as_str();
            TyTypePredicate {
                kind: if predicate.asserts {
                    TyTypePredicateKind::AssertsIdentifier
                } else {
                    TyTypePredicateKind::Identifier
                },
                parameter_name: Some(parameter_name),
                parameter_index: parameters
                    .iter()
                    .position(|parameter| parameter.name == parameter_name),
                target_type,
            }
        }
        TSTypePredicateName::This(_) => TyTypePredicate {
            kind: if predicate.asserts {
                TyTypePredicateKind::AssertsThis
            } else {
                TyTypePredicateKind::This
            },
            parameter_name: None,
            parameter_index: None,
            target_type,
        },
    }
}

pub(crate) fn type_predicate_kinds_match(
    source: &TyTypePredicate<'_>,
    target: &TyTypePredicate<'_>,
) -> bool {
    source.kind == target.kind && type_predicate_parameters_match(source, target)
}

fn type_predicate_parameters_match(
    source: &TyTypePredicate<'_>,
    target: &TyTypePredicate<'_>,
) -> bool {
    if source.parameter_index != target.parameter_index {
        return false;
    }
    source.parameter_index.is_some() || source.parameter_name == target.parameter_name
}

fn property_key_to_binding_pattern_string(key: &PropertyKey<'_>) -> Option<String> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.name.to_string()),
        PropertyKey::Identifier(identifier) => Some(identifier.name.to_string()),
        PropertyKey::NumericLiteral(literal) => literal.raw.as_ref().map(ToString::to_string),
        PropertyKey::StringLiteral(literal) => Some(format!("{:?}", literal.value.as_str())),
        _ => None,
    }
}

fn property_name_to_type_string(property: &TyProperty<'_>) -> String {
    let name = if property.computed {
        format!("[{}]", property.name)
    } else {
        property.name.to_string()
    };
    if property.optional {
        format!("{name}?")
    } else {
        name
    }
}

pub(crate) fn binding_pattern_to_parameter_name<'a>(
    arena: CheckerArena<'a>,
    pattern: &BindingPattern<'a>,
) -> &'a str {
    arena.str(&binding_pattern_to_string(pattern))
}

fn binding_pattern_to_string(pattern: &BindingPattern<'_>) -> String {
    match pattern {
        BindingPattern::BindingIdentifier(identifier) => identifier.name.to_string(),
        BindingPattern::ObjectPattern(object) => {
            let mut parts = object
                .properties
                .iter()
                .filter_map(binding_property_to_string)
                .collect::<Vec<_>>();
            if let Some(rest) = &object.rest {
                parts.push(format!("...{}", binding_pattern_to_string(&rest.argument)));
            }
            if parts.is_empty() {
                "{ }".to_string()
            } else {
                format!("{{ {}, }}", parts.join(", "))
            }
        }
        BindingPattern::ArrayPattern(array) => {
            let mut parts = array
                .elements
                .iter()
                .map(|element| {
                    element
                        .as_ref()
                        .map_or_else(String::new, binding_pattern_to_string)
                })
                .collect::<Vec<_>>();
            if let Some(rest) = &array.rest {
                parts.push(format!("...{}", binding_pattern_to_string(&rest.argument)));
            }
            format!("[{}]", parts.join(", "))
        }
        BindingPattern::AssignmentPattern(assignment) => {
            binding_pattern_to_string(&assignment.left)
        }
    }
}

fn binding_property_to_string(property: &oxc_ast::ast::BindingProperty<'_>) -> Option<String> {
    let key = property_key_to_binding_pattern_string(&property.key)?;
    let value = binding_pattern_to_string(&property.value);
    if property.shorthand || key == value {
        Some(key)
    } else {
        Some(format!("{key}: {value}"))
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
            Ty::r#union(arena, [Ty::boolean_true(), Ty::boolean()]),
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
    fn union_reduction_removes_never_from_multi_member_unions() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);

        assert_eq!(
            Ty::r#union(arena, [Ty::never(), Ty::undefined()]),
            Ty::undefined()
        );
        assert_eq!(Ty::r#union(arena, [Ty::never()]), Ty::never());
    }

    #[test]
    fn union_reduction_absorbs_literals_contained_by_template_literals() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let literal_template = Ty::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter([TemplateLiteralElement { value: "test" }]),
            expressions: arena.vec_from_iter([]),
        }));
        let pattern_template = Ty::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter([
                TemplateLiteralElement { value: "test" },
                TemplateLiteralElement { value: "" },
            ]),
            expressions: arena.vec_from_iter([Ty::string()]),
        }));

        assert_eq!(
            Ty::r#union(arena, [literal_template, pattern_template]).to_type_string(),
            "`test${string}`"
        );
        assert_eq!(
            Ty::r#union(arena, [Ty::string_literal(arena, "test"), pattern_template])
                .to_type_string(),
            "`test${string}`"
        );

        let backtracking_template = Ty::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter([
                TemplateLiteralElement { value: "" },
                TemplateLiteralElement { value: "a" },
                TemplateLiteralElement { value: "" },
            ]),
            expressions: arena.vec_from_iter([Ty::string(), Ty::string_literal(arena, "b")]),
        }));
        assert_eq!(
            Ty::r#union(
                arena,
                [Ty::string_literal(arena, "aab"), backtracking_template]
            )
            .to_type_string(),
            "`${string}a${\"b\"}`"
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

    #[test]
    fn object_method_display_uses_signature_syntax() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let abort_signal = Ty::type_reference(arena, "AbortSignal", []);
        let abort = TyProperty {
            name: "abort",
            ty: Ty::function(
                arena,
                [],
                [Ty::optional_parameter("reason", Ty::any())],
                abort_signal,
            ),
            computed: false,
            optional: false,
            method: true,
            readonly: false,
        };

        assert_eq!(
            Ty::object(arena, [abort]).to_type_string(),
            "{ abort(reason?: any): AbortSignal; }"
        );
    }

    #[test]
    fn object_readonly_property_display() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let readonly = TyProperty {
            name: "x",
            ty: Ty::string(),
            computed: false,
            optional: false,
            method: false,
            readonly: true,
        };

        assert_eq!(
            Ty::object(arena, [readonly]).to_type_string(),
            "{ readonly x: string; }"
        );
    }

    #[test]
    fn conditional_infer_extracts_direct_type() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let u = Ty::type_parameter("U", None, None);

        let ty = Ty::conditional(
            arena,
            Ty::string(),
            Ty::infer(arena, u),
            Ty::type_reference(arena, "U", []),
            Ty::never(),
            false,
        );

        assert_eq!(ty, Ty::string());
    }

    #[test]
    fn conditional_infer_extracts_object_property_type() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let u = Ty::type_parameter("U", None, None);

        let ty = Ty::conditional(
            arena,
            Ty::object(arena, [Ty::property("value", Ty::number())]),
            Ty::object(arena, [Ty::property("value", Ty::infer(arena, u))]),
            Ty::type_reference(arena, "U", []),
            Ty::never(),
            false,
        );

        assert_eq!(ty, Ty::number());
    }

    #[test]
    fn conditional_infer_constraint_can_fail() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let u = Ty::type_parameter("U", Some(Ty::string()), None);

        let ty = Ty::conditional(
            arena,
            Ty::number(),
            Ty::infer(arena, u),
            Ty::type_reference(arena, "U", []),
            Ty::never(),
            false,
        );

        assert_eq!(ty, Ty::never());
    }

    #[test]
    fn conditional_infer_merges_repeated_candidates() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let u = Ty::type_parameter("U", None, None);

        let ty = Ty::conditional(
            arena,
            Ty::object(
                arena,
                [
                    Ty::property("a", Ty::string()),
                    Ty::property("b", Ty::number()),
                ],
            ),
            Ty::object(
                arena,
                [
                    Ty::property("a", Ty::infer(arena, u)),
                    Ty::property("b", Ty::infer(arena, u)),
                ],
            ),
            Ty::type_reference(arena, "U", []),
            Ty::never(),
            false,
        );

        assert_eq!(ty.to_type_string(), "string | number");
    }

    #[test]
    fn conditional_infer_extracts_tuple_rest() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let head = Ty::type_parameter("Head", None, None);
        let rest = Ty::type_parameter("Rest", None, None);

        let ty = Ty::conditional(
            arena,
            Ty::tuple(
                arena,
                vec![
                    TupleElement::Regular(Ty::string()),
                    TupleElement::Regular(Ty::number()),
                ],
            ),
            Ty::tuple(
                arena,
                vec![
                    TupleElement::Regular(Ty::infer(arena, head)),
                    TupleElement::Rest(Ty::infer(arena, rest)),
                ],
            ),
            Ty::type_reference(arena, "Rest", []),
            Ty::never(),
            false,
        );

        assert_eq!(ty.to_type_string(), "[number]");
    }

    #[test]
    fn conditional_infer_shadows_outer_type_parameter_substitution() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let outer_array = Ty::array(arena, Ty::string());
        let conditional = Ty::conditional(
            arena,
            Ty::type_reference(arena, "T", []),
            Ty::array(arena, Ty::infer(arena, Ty::type_parameter("T", None, None))),
            Ty::type_reference(arena, "T", []),
            Ty::never(),
            false,
        );
        let substitutions = HashMap::from([("T", outer_array)]);

        assert_eq!(
            conditional.substitute_type_parameters(arena, &substitutions),
            Ty::string()
        );
    }
}
