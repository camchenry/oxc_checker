use crate::{
    limits::{TYPE_STRING_DEPTH, TYPE_STRING_MAX_DEPTH, TYPE_VISIT_MAX_DEPTH},
    type_set::{reduce_intersection_type, reduce_union_type},
};
use num_traits::{Zero, cast::ToPrimitive};
use oxc_allocator::{Allocator, Vec as ArenaVec};
use oxc_ast::ast::{
    BindingPattern, NumberBase, PropertyKey, TSMappedTypeModifierOperator, TSType,
    TSTypeAnnotation, TSTypePredicate, TSTypePredicateName,
};
use oxc_str::Str;

const SYNTHETIC_INDEX_SIGNATURE_NAME: &str = "x";

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
    pub fn is_empty(&self) -> bool {
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

pub(crate) fn function_minimum_argument_count(function: &TyFunction<'_>) -> usize {
    let fixed_required = function
        .parameters
        .iter()
        .filter(|parameter| !parameter.optional && !parameter.rest)
        .count();
    fixed_required
        + function
            .parameters
            .iter()
            .find(|parameter| parameter.rest)
            .map_or(0, |parameter| {
                rest_tuple_minimum_argument_count(parameter.ty)
            })
}

pub(crate) fn function_maximum_argument_count(function: &TyFunction<'_>) -> Option<usize> {
    let Some(rest_index) = function
        .parameters
        .iter()
        .position(|parameter| parameter.rest)
    else {
        return Some(function.parameters.len());
    };
    rest_tuple_maximum_argument_count(function.parameters[rest_index].ty)
        .map(|rest_count| rest_index + rest_count)
}

pub(crate) fn function_parameter_type_at_call_index<'a>(
    function: &TyFunction<'a>,
    index: usize,
) -> Option<Ty<'a>> {
    if let Some(rest_index) = function
        .parameters
        .iter()
        .position(|parameter| parameter.rest)
        && index >= rest_index
    {
        return rest_parameter_type_at_call_index(
            function.parameters[rest_index].ty,
            index - rest_index,
        );
    }

    function.parameters.get(index).map(|parameter| parameter.ty)
}

fn rest_tuple_minimum_argument_count(ty: Ty<'_>) -> usize {
    let Ty::Tuple(tuple) = ty else {
        return 0;
    };
    tuple
        .elements
        .iter()
        .take_while(|element| !matches!(element, TupleElement::Rest(_)))
        .filter(|element| matches!(element, TupleElement::Regular(_)))
        .count()
}

fn rest_tuple_maximum_argument_count(ty: Ty<'_>) -> Option<usize> {
    let Ty::Tuple(tuple) = ty else {
        return None;
    };
    if tuple
        .elements
        .iter()
        .any(|element| matches!(element, TupleElement::Rest(_)))
    {
        None
    } else {
        Some(tuple.elements.len())
    }
}

fn rest_parameter_type_at_call_index<'a>(ty: Ty<'a>, index: usize) -> Option<Ty<'a>> {
    let Ty::Tuple(tuple) = ty else {
        return Some(ty.array_element_type().unwrap_or(ty));
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
                    return Some(ty.array_element_type().unwrap_or(*ty));
                }
            }
        }
    }

    None
}

#[derive(Debug, Eq)]
pub struct TyTypeReference<'a> {
    pub(crate) name: &'a str,
    pub(crate) type_arguments: ArenaVec<'a, Ty<'a>>,
    pub(crate) display_type_argument_count: usize,
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

#[derive(Debug, Clone, Copy)]
pub struct TyNumberLiteral<'a> {
    /// Value of the number literal, converted to base-10 floating point.
    pub(crate) value: f64,
    /// The number as it appears in source code
    ///
    /// Can be `None` if the number literal is not directly from the source code
    pub(crate) raw: Option<Str<'a>>,
    /// The base representation used by the literal in source code
    pub(crate) base: NumberBase,
}

impl<'a> TyNumberLiteral<'a> {
    pub fn to_usize(&self) -> Option<usize> {
        self.value.to_usize()
    }
}

impl PartialEq for TyNumberLiteral<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.value.total_cmp(&other.value) == std::cmp::Ordering::Equal
            && self.raw == other.raw
            && self.base == other.base
    }
}
impl Eq for TyNumberLiteral<'_> {}

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
pub struct TemplateLiteralElement<'a> {
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

// TODO: Allow early return so we don't visit unnecessary nodes
pub(crate) fn visit_type<'a>(ty: Ty<'a>, f: &mut impl FnMut(Ty<'a>)) {
    visit_type_at_depth(ty, f, 0);
}

fn visit_type_at_depth<'a>(ty: Ty<'a>, f: &mut impl FnMut(Ty<'a>), depth: usize) {
    if depth >= TYPE_VISIT_MAX_DEPTH {
        return;
    }

    f(ty);
    let next_depth = depth + 1;
    match ty {
        Ty::Object(object) => {
            for property in &object.properties {
                visit_type_at_depth(property.ty, f, next_depth);
            }
            for signature in &object.signatures {
                visit_type_at_depth(Ty::Function(signature.function), f, next_depth);
            }
            for info in &object.index_infos {
                visit_type_at_depth(info.key_type, f, next_depth);
                visit_type_at_depth(info.value_type, f, next_depth);
            }
        }
        Ty::ModuleNamespace(namespace) => {
            for property in &namespace.properties {
                visit_type_at_depth(property.ty, f, next_depth);
            }
        }
        Ty::Function(function) => {
            for type_parameter in &function.type_parameters {
                if let Some(constraint_type) = type_parameter.constraint_type {
                    visit_type_at_depth(constraint_type, f, next_depth);
                }
                if let Some(default_type) = type_parameter.default_type {
                    visit_type_at_depth(default_type, f, next_depth);
                }
            }
            for parameter in &function.parameters {
                visit_type_at_depth(parameter.ty, f, next_depth);
            }
            visit_type_at_depth(function.return_type, f, next_depth);
            if let Some(target_type) = function
                .type_predicate
                .and_then(|predicate| predicate.target_type)
            {
                visit_type_at_depth(target_type, f, next_depth);
            }
        }
        Ty::TypeReference(reference) => {
            for ty in &reference.type_arguments {
                visit_type_at_depth(*ty, f, next_depth);
            }
        }
        Ty::TypeQuery(query) => {
            visit_type_at_depth(query.resolved, f, next_depth);
            for ty in &query.type_arguments {
                visit_type_at_depth(*ty, f, next_depth);
            }
        }
        Ty::TemplateLiteral(template_literal) => {
            for ty in &template_literal.expressions {
                visit_type_at_depth(*ty, f, next_depth);
            }
        }
        Ty::Array(array) => visit_type_at_depth(array.element_type, f, next_depth),
        Ty::Tuple(tuple) => {
            for element in &tuple.elements {
                visit_type_at_depth(element.ty(), f, next_depth);
            }
        }
        Ty::Union(union) => {
            for ty in &union.types {
                visit_type_at_depth(*ty, f, next_depth);
            }
        }
        Ty::Intersection(intersection) => {
            for ty in &intersection.types {
                visit_type_at_depth(*ty, f, next_depth);
            }
        }
        Ty::Keyof(keyof) => visit_type_at_depth(keyof.target, f, next_depth),
        Ty::IndexedAccess(indexed_access) => {
            visit_type_at_depth(indexed_access.object_type, f, next_depth);
            visit_type_at_depth(indexed_access.index_type, f, next_depth);
        }
        Ty::Conditional(conditional) => {
            visit_type_at_depth(conditional.check_type, f, next_depth);
            visit_type_at_depth(conditional.extends_type, f, next_depth);
            visit_type_at_depth(conditional.true_type, f, next_depth);
            visit_type_at_depth(conditional.false_type, f, next_depth);
        }
        Ty::Infer(infer) => {
            if let Some(constraint_type) = infer.type_parameter.constraint_type {
                visit_type_at_depth(constraint_type, f, next_depth);
            }
            if let Some(default_type) = infer.type_parameter.default_type {
                visit_type_at_depth(default_type, f, next_depth);
            }
        }
        Ty::Mapped(mapped) => {
            visit_type_at_depth(mapped.constraint, f, next_depth);
            if let Some(name_type) = mapped.name_type {
                visit_type_at_depth(name_type, f, next_depth);
            }
            visit_type_at_depth(mapped.template, f, next_depth);
        }
        _ => {}
    }
}

impl<'a> Ty<'a> {
    pub fn none() -> Self {
        Self::None
    }

    pub fn number() -> Self {
        Self::Number
    }

    pub fn number_literal(
        arena: CheckerArena<'a>,
        value: f64,
        raw: &'a str,
        base: NumberBase,
    ) -> Self {
        Self::NumberLiteral(arena.alloc(TyNumberLiteral {
            value,
            raw: Some(*arena.alloc(Str::from(raw))),
            base,
        }))
    }

    pub fn number_literal_from_ast(
        arena: CheckerArena<'a>,
        lit: &'a oxc_ast::ast::NumericLiteral,
        negated: bool,
    ) -> Self {
        // TODO: Do we need to store `-` in the raw string?
        let value = if negated { -lit.value } else { lit.value };
        Self::NumberLiteral(arena.alloc(TyNumberLiteral {
            value,
            raw: lit.raw,
            base: lit.base,
        }))
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
        quasis: impl IntoIterator<Item = TemplateLiteralElement<'a>>,
        expressions: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        Self::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter(quasis),
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
        Self::object_with_signatures_and_index_infos(
            arena,
            properties,
            std::iter::empty(),
            std::iter::empty(),
        )
    }

    pub fn object_with_signatures(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
        signatures: impl IntoIterator<Item = Signature<'a>>,
    ) -> Self {
        Self::object_with_signatures_and_index_infos(
            arena,
            properties,
            signatures,
            std::iter::empty(),
        )
    }

    pub fn object_with_index_infos(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
        index_infos: impl IntoIterator<Item = IndexInfo<'a>>,
    ) -> Self {
        Self::object_with_signatures_and_index_infos(
            arena,
            properties,
            std::iter::empty(),
            index_infos,
        )
    }

    pub fn object_with_signatures_and_index_infos(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
        signatures: impl IntoIterator<Item = Signature<'a>>,
        index_infos: impl IntoIterator<Item = IndexInfo<'a>>,
    ) -> Self {
        Self::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(properties),
            signatures: arena.vec_from_iter(signatures),
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
        let type_arguments = arena.vec_from_iter(type_arguments);
        let display_type_argument_count = type_arguments.len();
        Self::TypeReference(arena.alloc(TyTypeReference {
            name,
            type_arguments,
            display_type_argument_count,
        }))
    }

    pub(crate) fn type_reference_with_display_type_argument_count(
        arena: CheckerArena<'a>,
        name: &'a str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
        display_type_argument_count: usize,
    ) -> Self {
        let type_arguments = arena.vec_from_iter(type_arguments);
        let display_type_argument_count = display_type_argument_count.min(type_arguments.len());
        Self::TypeReference(arena.alloc(TyTypeReference {
            name,
            type_arguments,
            display_type_argument_count,
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

    /// Returns the constant union type of all possible `typeof` values.
    /// `"string" | "number" | "bigint" | "boolean" | "symbol" | "undefined" | "object" | "function"`
    pub fn typeof_string_values(arena: CheckerArena<'a>) -> Self {
        Self::r#union(
            arena,
            [
                Self::string_literal(arena, "string"),
                Self::string_literal(arena, "number"),
                Self::string_literal(arena, "bigint"),
                Self::string_literal(arena, "boolean"),
                Self::string_literal(arena, "symbol"),
                Self::string_literal(arena, "undefined"),
                Self::string_literal(arena, "object"),
                Self::string_literal(arena, "function"),
            ],
        )
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

    pub(crate) fn is_transparent_type_alias_union_constituent(&self) -> bool {
        matches!(
            self,
            Self::String
                | Self::Number
                | Self::Boolean
                | Self::Bigint
                | Self::Symbol
                | Self::Undefined
                | Self::Null
                | Self::Void
                | Self::Never
                | Self::Any
                | Self::Unknown
                | Self::PrimitiveObject
                | Self::StringLiteral(_)
                | Self::NumberLiteral(_)
                | Self::BooleanLiteral(_)
                | Self::BigIntLiteral(_)
                | Self::TemplateLiteral(_)
                | Self::UniqueSymbol(_)
        )
    }

    /// Returns `true` if the type is a numerical index type.
    pub fn is_number_index_type(&self) -> bool {
        matches!(self, Ty::Number | Ty::NumberLiteral(_))
    }

    pub(crate) fn property_type(&self, arena: CheckerArena<'a>, name: &str) -> Option<Self> {
        // TODO(correctness): handle all readonly/optional cases
        match self {
            Self::Object(object) => object.properties.iter().find_map(|property| {
                (property.name == name && !property.computed).then_some(if property.optional {
                    Self::union(arena, [property.ty, Self::Undefined])
                } else {
                    property.ty
                })
            }),
            Self::ModuleNamespace(namespace) => namespace.properties.iter().find_map(|property| {
                (property.name == name && !property.computed).then_some(if property.optional {
                    Self::union(arena, [property.ty, Self::Undefined])
                } else {
                    property.ty
                })
            }),
            Self::Intersection(intersection) => intersection
                .types
                .iter()
                .find_map(|ty| ty.property_type(arena, name)),
            _ => None,
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
        TYPE_STRING_DEPTH.with(|depth| {
            let current = depth.get();
            if current >= TYPE_STRING_MAX_DEPTH {
                return "...".to_string();
            }

            depth.set(current + 1);
            let result = self.to_type_string_inner();
            depth.set(current);
            result
        })
    }

    fn to_type_string_inner(self) -> String {
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
                            "{}[{}: {}]: {};",
                            readonly,
                            info.name,
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
                if reference.display_type_argument_count == 0 {
                    reference.name.to_string()
                } else {
                    let type_arguments = reference
                        .type_arguments
                        .iter()
                        .take(reference.display_type_argument_count)
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
            Self::NumberLiteral(number_literal) => {
                // Print the base-10 representation of the number
                if number_literal.value.is_zero() {
                    // Treat +0 and -0 as the same when printing.
                    "0".to_string()
                } else {
                    number_literal.value.to_string()
                }
            }
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
                let extends_type = if matches!(conditional.extends_type, Self::Conditional(_)) {
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
            Self::Mapped(mapped) => {
                let mut s = String::from("{ ");
                let prefix = match mapped.readonly {
                    MappedModifier::None => "",
                    MappedModifier::True => "readonly ",
                    MappedModifier::Plus => "+readonly ",
                    MappedModifier::Minus => "-readonly ",
                };
                s.push_str(prefix);
                s.push('[');
                s.push_str(mapped.key);
                s.push_str(" in ");
                s.push_str(&mapped.constraint.to_type_string());
                if let Some(name_type) = mapped.name_type {
                    s.push_str(" as ");
                    s.push_str(&name_type.to_type_string());
                }
                s.push(']');
                let suffix = match mapped.optional {
                    MappedModifier::None => "",
                    MappedModifier::True => "?",
                    MappedModifier::Plus => "+?",
                    MappedModifier::Minus => "-?",
                };
                s.push_str(suffix);
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
            Self::Function(_)
                | Self::Union(_)
                | Self::Intersection(_)
                | Self::Conditional(_)
                | Self::Infer(_)
        )
    }

    pub(crate) fn with_implicit_type_arguments_visible(self, arena: CheckerArena<'a>) -> Self {
        match self {
            Self::TypeReference(reference) => {
                let display_type_argument_count = if reference.display_type_argument_count == 0 {
                    reference.type_arguments.len()
                } else {
                    reference.display_type_argument_count
                };
                Self::type_reference_with_display_type_argument_count(
                    arena,
                    reference.name,
                    reference
                        .type_arguments
                        .iter()
                        .map(|ty| ty.with_implicit_type_arguments_visible(arena)),
                    display_type_argument_count,
                )
            }
            Self::Union(union) => Self::r#union(
                arena,
                union
                    .types
                    .iter()
                    .map(|ty| ty.with_implicit_type_arguments_visible(arena)),
            ),
            Self::Intersection(intersection) => Self::intersection(
                arena,
                intersection
                    .types
                    .iter()
                    .map(|ty| ty.with_implicit_type_arguments_visible(arena)),
            ),
            Self::Array(array) => {
                let element_type = array
                    .element_type
                    .with_implicit_type_arguments_visible(arena);
                if array.readonly {
                    Self::readonly_array(arena, element_type)
                } else {
                    Self::array(arena, element_type)
                }
            }
            Self::Tuple(tuple) => {
                let elements = tuple
                    .elements
                    .iter()
                    .map(|element| match element {
                        TupleElement::Regular(ty) => {
                            TupleElement::Regular(ty.with_implicit_type_arguments_visible(arena))
                        }
                        TupleElement::Rest(ty) => {
                            TupleElement::Rest(ty.with_implicit_type_arguments_visible(arena))
                        }
                        TupleElement::Optional(ty) => {
                            TupleElement::Optional(ty.with_implicit_type_arguments_visible(arena))
                        }
                    })
                    .collect::<Vec<_>>();
                if tuple.readonly {
                    Self::readonly_tuple(arena, elements)
                } else {
                    Self::tuple(arena, elements)
                }
            }
            _ => self,
        }
    }

    pub(crate) fn with_signatures(
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

    pub(crate) fn with_index_infos(
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

    /// Returns the index infos of the type, or `None` if the type is not an object with index infos.
    pub fn index_infos(&self) -> Option<&[IndexInfo<'a>]> {
        let Ty::Object(object) = self else {
            return None;
        };
        if object.index_infos.is_empty() {
            None
        } else {
            Some(&object.index_infos)
        }
    }

    /// Returns the element type of an array type, or `None` if the type is not an array.
    pub fn array_element_type(&self) -> Option<Self> {
        let Ty::Array(array) = self else {
            return None;
        };
        Some(array.element_type)
    }

    /// Returns the string value of the type (if applicable).
    pub fn string_value(&self) -> Option<&str> {
        match self {
            // Remove quoting
            Ty::StringLiteral(string_literal) => Some(
                string_literal
                    .value
                    .strip_prefix('\'')
                    .and_then(|name| name.strip_suffix('\''))
                    .or_else(|| {
                        string_literal
                            .value
                            .strip_prefix('"')
                            .and_then(|name| name.strip_suffix('"'))
                    })
                    .unwrap_or(string_literal.value),
            ),
            // TODO(completeness): Handle template literals
            _ => None,
        }
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

    if contains_unresolved_type_variable(check_type)
        || contains_unresolved_type_variable(extends_type)
        || contains_infer(check_type)
        || contains_infer(extends_type)
    {
        return Ty::Conditional(arena.alloc(TyConditional {
            check_type,
            extends_type,
            true_type,
            false_type,
            is_distributive,
        }));
    }

    if crate::relations::is_assignable_to_without_checker(check_type, extends_type) {
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
    if contains_unresolved_type_variable(check_return.extends_type)
        || contains_unresolved_type_variable(extends_return.extends_type)
    {
        return None;
    }

    Some(
        crate::relations::is_assignable_to_without_checker(
            check_return.extends_type,
            extends_return.extends_type,
        ) && crate::relations::is_assignable_to_without_checker(
            extends_return.extends_type,
            check_return.extends_type,
        ),
    )
}

fn contains_unresolved_type_variable(ty: Ty<'_>) -> bool {
    let mut contains = false;
    visit_type(ty, &mut |ty| match ty {
        Ty::TypeReference(reference) if reference.type_arguments.is_empty() => contains = true,
        Ty::Function(function) if !function.type_parameters.is_empty() => contains = true,
        Ty::Infer(_) => contains = true,
        _ => {}
    });
    contains
}

fn contains_infer(ty: Ty<'_>) -> bool {
    let mut contains = false;
    visit_type(ty, &mut |ty| {
        contains |= matches!(ty, Ty::Infer(_));
    });
    contains
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
    /// The name of the index parameter.
    pub(crate) name: &'a str,
    /// The type of the index key. The `K` in `{ [k: K]: V }` or `string` in `{ [k: string]: number }`
    pub(crate) key_type: Ty<'a>,
    /// The type of the index value. The `V` in `{ [k: K]: V }` or `string` in `{ [k: string]: number }`
    pub(crate) value_type: Ty<'a>,
    /// Whether the index returns a readonly value.
    pub(crate) readonly: bool,
}

impl<'a> IndexInfo<'a> {
    pub(crate) fn new(name: &'a str, key_type: Ty<'a>, value_type: Ty<'a>, readonly: bool) -> Self {
        Self {
            name,
            key_type,
            value_type,
            readonly,
        }
    }

    pub(crate) fn synthetic(key_type: Ty<'a>, value_type: Ty<'a>, readonly: bool) -> Self {
        Self::new(
            SYNTHETIC_INDEX_SIGNATURE_NAME,
            key_type,
            value_type,
            readonly,
        )
    }
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
        .flat_map(function_parameter_to_type_strings)
        .collect::<Vec<_>>()
        .join(", ");
    (type_parameters, parameters)
}

fn function_parameter_to_type_strings(parameter: &TyParameter<'_>) -> Vec<String> {
    if parameter.rest
        && let Ty::Tuple(tuple) = parameter.ty
        && !tuple
            .elements
            .iter()
            .any(|element| matches!(element, TupleElement::Rest(_)))
    {
        return tuple
            .elements
            .iter()
            .enumerate()
            .map(|(index, element)| {
                let name = format!("{}_{}", parameter.name, index);
                match element {
                    TupleElement::Regular(ty) => format!("{name}: {}", ty.to_type_string()),
                    TupleElement::Optional(ty) => format!("{name}?: {}", ty.to_type_string()),
                    TupleElement::Rest(ty) => format!("...{name}: {}", ty.to_type_string()),
                }
            })
            .collect();
    }

    if parameter.rest {
        vec![format!(
            "...{}: {}",
            parameter.name,
            parameter.ty.to_type_string()
        )]
    } else if parameter.optional {
        vec![format!(
            "{}?: {}",
            parameter.name,
            parameter.ty.to_type_string()
        )]
    } else {
        vec![format!(
            "{}: {}",
            parameter.name,
            parameter.ty.to_type_string()
        )]
    }
}

pub(crate) fn return_type_and_type_predicate_from_annotation_with_resolver<'a>(
    parameters: &[TyParameter<'a>],
    return_type: Option<&'a TSTypeAnnotation<'a>>,
    resolve_type_annotation: impl Fn(&'a TSTypeAnnotation<'a>) -> Ty<'a>,
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
            Ty::r#union(
                arena,
                [
                    Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal),
                    Ty::number()
                ]
            ),
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
}
