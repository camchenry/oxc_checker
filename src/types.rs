use crate::{
    limits::{TYPE_STRING_MAX_DEPTH, TYPE_VISIT_MAX_DEPTH},
    type_set::{reduce_intersection_type, reduce_union_type},
};
use bitflags::bitflags;
use num_traits::{Zero, cast::ToPrimitive};
use oxc_allocator::{Allocator, Vec as ArenaVec};
use oxc_ast::ast::{
    BindingPattern, NumberBase, PropertyKey, TSMappedTypeModifierOperator, TSType,
    TSTypeAnnotation, TSTypePredicate, TSTypePredicateName,
};
use oxc_index::Idx;
use oxc_str::Str;
use std::{
    cell::{Cell, RefCell},
    marker::PhantomData,
    num::NonZeroU32,
};

const SYNTHETIC_INDEX_SIGNATURE_NAME: &str = "x";

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct TypeFormatFlags: u8 {
        const NONE = 0;
        const WRITE_ARRAY_AS_GENERIC_TYPE = 1 << 0;
    }
}

#[derive(Clone, Copy)]
pub struct CheckerArena<'a> {
    allocator: &'a Allocator,
    types: &'a RefCell<ArenaVec<'a, TypeData<'a>>>,
}

impl<'a> CheckerArena<'a> {
    pub fn new(allocator: &'a Allocator) -> Self {
        let types = allocator.alloc(RefCell::new(ArenaVec::new_in(allocator)));
        let arena = Self { allocator, types };
        {
            let mut types = arena.types.borrow_mut();
            for data in [
                TypeData::None,
                TypeData::Number,
                TypeData::String,
                TypeData::Boolean,
                TypeData::Bigint,
                TypeData::Symbol,
                TypeData::Undefined,
                TypeData::Null,
                TypeData::Any,
                TypeData::Unknown,
                TypeData::Void,
                TypeData::Never,
                TypeData::PrimitiveObject,
                TypeData::This,
                TypeData::BooleanLiteral(false),
                TypeData::BooleanLiteral(true),
            ] {
                types.push(data);
            }
        }
        arena
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

    pub(crate) fn alloc_type(&self, data: TypeData<'a>) -> Ty<'a> {
        let mut types = self.types.borrow_mut();
        let ty = Ty::from_index(types.len());
        types.push(data);
        ty
    }

    pub(crate) fn type_data(&self, ty: Ty<'a>) -> TypeData<'a> {
        self.types.borrow()[ty.id().index()]
    }

    pub fn type_count(&self) -> usize {
        self.types.borrow().len()
    }

    pub fn types(&self) -> impl ExactSizeIterator<Item = Ty<'a>> {
        (0..self.type_count()).map(Ty::from_index)
    }

    pub fn type_ids(&self) -> impl ExactSizeIterator<Item = TypeId> {
        self.types().map(Ty::id)
    }

    pub fn type_from_id(&self, id: TypeId) -> Option<Ty<'a>> {
        (id.index() < self.type_count()).then(|| Ty::from_id(id))
    }

    /// Compares the complete structure of two types from this checker arena.
    pub fn is_type_identical_to(&self, left: Ty<'a>, right: Ty<'a>) -> bool {
        TypeIdentity::new(*self).compare(left, right)
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(NonZeroU32);

impl TypeId {
    pub const fn index(self) -> usize {
        self.0.get() as usize - 1
    }

    pub const fn get(self) -> u32 {
        self.0.get()
    }
}

impl Idx for TypeId {
    const MAX: usize = u32::MAX as usize - 1;

    unsafe fn from_usize_unchecked(index: usize) -> Self {
        Self(NonZeroU32::new(index as u32 + 1).expect("type IDs must be nonzero"))
    }

    fn index(self) -> usize {
        Self::index(self)
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ty<'a> {
    id: TypeId,
    marker: PhantomData<&'a ()>,
}

impl<'a> Ty<'a> {
    const fn from_raw(raw: u32) -> Self {
        let Some(raw) = NonZeroU32::new(raw) else {
            panic!("type IDs must be nonzero")
        };
        Self {
            id: TypeId(raw),
            marker: PhantomData,
        }
    }

    fn from_index(index: usize) -> Self {
        let raw = u32::try_from(index + 1).expect("type ID overflow");
        Self::from_raw(raw)
    }

    const fn from_id(id: TypeId) -> Self {
        Self {
            id,
            marker: PhantomData,
        }
    }

    pub const fn id(self) -> TypeId {
        self.id
    }

    #[allow(non_upper_case_globals)]
    pub const None: Self = Self::from_raw(1);
    #[allow(non_upper_case_globals)]
    pub const Number: Self = Self::from_raw(2);
    #[allow(non_upper_case_globals)]
    pub const String: Self = Self::from_raw(3);
    #[allow(non_upper_case_globals)]
    pub const Boolean: Self = Self::from_raw(4);
    #[allow(non_upper_case_globals)]
    pub const Bigint: Self = Self::from_raw(5);
    #[allow(non_upper_case_globals)]
    pub const Symbol: Self = Self::from_raw(6);
    #[allow(non_upper_case_globals)]
    pub const Undefined: Self = Self::from_raw(7);
    #[allow(non_upper_case_globals)]
    pub const Null: Self = Self::from_raw(8);
    #[allow(non_upper_case_globals)]
    pub const Any: Self = Self::from_raw(9);
    #[allow(non_upper_case_globals)]
    pub const Unknown: Self = Self::from_raw(10);
    #[allow(non_upper_case_globals)]
    pub const Void: Self = Self::from_raw(11);
    #[allow(non_upper_case_globals)]
    pub const Never: Self = Self::from_raw(12);
    #[allow(non_upper_case_globals)]
    pub const PrimitiveObject: Self = Self::from_raw(13);
    #[allow(non_upper_case_globals)]
    pub const This: Self = Self::from_raw(14);

    const BOOLEAN_FALSE: Self = Self::from_raw(15);
    const BOOLEAN_TRUE: Self = Self::from_raw(16);
}

#[repr(C, u8)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum TypeData<'a> {
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

pub(crate) fn function_minimum_argument_count<'a>(
    arena: CheckerArena<'a>,
    function: &TyFunction<'a>,
) -> usize {
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
                rest_tuple_minimum_argument_count(arena, parameter.ty)
            })
}

pub(crate) fn function_maximum_argument_count<'a>(
    arena: CheckerArena<'a>,
    function: &TyFunction<'a>,
) -> Option<usize> {
    let Some(rest_index) = function
        .parameters
        .iter()
        .position(|parameter| parameter.rest)
    else {
        return Some(function.parameters.len());
    };
    rest_tuple_maximum_argument_count(arena, function.parameters[rest_index].ty)
        .map(|rest_count| rest_index + rest_count)
}

pub(crate) fn function_parameter_type_at_call_index<'a>(
    arena: CheckerArena<'a>,
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
            arena,
            function.parameters[rest_index].ty,
            index - rest_index,
        );
    }

    function.parameters.get(index).map(|parameter| parameter.ty)
}

fn rest_tuple_minimum_argument_count<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> usize {
    let TypeData::Tuple(tuple) = arena.type_data(ty) else {
        return 0;
    };
    tuple
        .elements
        .iter()
        .take_while(|element| !matches!(element, TupleElement::Rest(_)))
        .filter(|element| matches!(element, TupleElement::Regular(_)))
        .count()
}

fn rest_tuple_maximum_argument_count<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> Option<usize> {
    let TypeData::Tuple(tuple) = arena.type_data(ty) else {
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

fn rest_parameter_type_at_call_index<'a>(
    arena: CheckerArena<'a>,
    ty: Ty<'a>,
    index: usize,
) -> Option<Ty<'a>> {
    let TypeData::Tuple(tuple) = arena.type_data(ty) else {
        return Some(ty.array_element_type(arena).unwrap_or(ty));
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
                    return Some(ty.array_element_type(arena).unwrap_or(*ty));
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
    /// Whether to display this array using `Array<T>` or `ReadonlyArray<T>` syntax.
    pub(crate) display_as_generic: bool,
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

struct TypeIdentity<'a> {
    arena: CheckerArena<'a>,
    active: Vec<(TypeId, TypeId)>,
}

impl<'a> TypeIdentity<'a> {
    fn new(arena: CheckerArena<'a>) -> Self {
        Self {
            arena,
            active: Vec::new(),
        }
    }

    fn compare(&mut self, left: Ty<'a>, right: Ty<'a>) -> bool {
        if left == right {
            return true;
        }

        let pair = (left.id(), right.id());
        if self
            .active
            .iter()
            .any(|active| *active == pair || *active == (pair.1, pair.0))
        {
            return true;
        }

        self.active.push(pair);
        let identical = match (self.arena.type_data(left), self.arena.type_data(right)) {
            (TypeData::None, TypeData::None)
            | (TypeData::Number, TypeData::Number)
            | (TypeData::String, TypeData::String)
            | (TypeData::Boolean, TypeData::Boolean)
            | (TypeData::Bigint, TypeData::Bigint)
            | (TypeData::Symbol, TypeData::Symbol)
            | (TypeData::Undefined, TypeData::Undefined)
            | (TypeData::Null, TypeData::Null)
            | (TypeData::Any, TypeData::Any)
            | (TypeData::Unknown, TypeData::Unknown)
            | (TypeData::Void, TypeData::Void)
            | (TypeData::Never, TypeData::Never)
            | (TypeData::PrimitiveObject, TypeData::PrimitiveObject)
            | (TypeData::This, TypeData::This) => true,
            (TypeData::UniqueSymbol(left), TypeData::UniqueSymbol(right)) => left == right,
            (TypeData::Object(left), TypeData::Object(right)) => {
                self.objects_are_identical(left, right)
            }
            (TypeData::ModuleNamespace(left), TypeData::ModuleNamespace(right)) => {
                left.name == right.name
                    && self.properties_are_identical(&left.properties, &right.properties)
            }
            (TypeData::Function(left), TypeData::Function(right)) => {
                self.functions_are_identical(left, right)
            }
            (TypeData::TypeReference(left), TypeData::TypeReference(right)) => {
                left.name == right.name
                    && self.types_are_identical(&left.type_arguments, &right.type_arguments)
            }
            (TypeData::TypeQuery(left), TypeData::TypeQuery(right)) => {
                left.name == right.name
                    && self.compare(left.resolved, right.resolved)
                    && self.types_are_identical(&left.type_arguments, &right.type_arguments)
            }
            (TypeData::StringLiteral(left), TypeData::StringLiteral(right)) => left == right,
            (TypeData::NumberLiteral(left), TypeData::NumberLiteral(right)) => left == right,
            (TypeData::BooleanLiteral(left), TypeData::BooleanLiteral(right)) => left == right,
            (TypeData::BigIntLiteral(left), TypeData::BigIntLiteral(right)) => left == right,
            (TypeData::TemplateLiteral(left), TypeData::TemplateLiteral(right)) => {
                left.quasis == right.quasis
                    && self.types_are_identical(&left.expressions, &right.expressions)
            }
            (TypeData::Array(left), TypeData::Array(right)) => {
                left.readonly == right.readonly
                    && self.compare(left.element_type, right.element_type)
            }
            (TypeData::Tuple(left), TypeData::Tuple(right)) => {
                left.readonly == right.readonly
                    && left.elements.len() == right.elements.len()
                    && left
                        .elements
                        .iter()
                        .zip(&right.elements)
                        .all(|(left, right)| self.tuple_elements_are_identical(left, right))
            }
            (TypeData::Union(left), TypeData::Union(right)) => {
                self.types_are_identical(&left.types, &right.types)
            }
            (TypeData::Intersection(left), TypeData::Intersection(right)) => {
                self.types_are_identical(&left.types, &right.types)
            }
            (TypeData::Keyof(left), TypeData::Keyof(right)) => {
                self.compare(left.target, right.target)
            }
            (TypeData::IndexedAccess(left), TypeData::IndexedAccess(right)) => {
                self.compare(left.object_type, right.object_type)
                    && self.compare(left.index_type, right.index_type)
            }
            (TypeData::Conditional(left), TypeData::Conditional(right)) => {
                left.is_distributive == right.is_distributive
                    && self.compare(left.check_type, right.check_type)
                    && self.compare(left.extends_type, right.extends_type)
                    && self.compare(left.true_type, right.true_type)
                    && self.compare(left.false_type, right.false_type)
            }
            (TypeData::Infer(left), TypeData::Infer(right)) => {
                self.type_parameters_are_identical(&left.type_parameter, &right.type_parameter)
            }
            (TypeData::Mapped(left), TypeData::Mapped(right)) => {
                left.key == right.key
                    && left.optional == right.optional
                    && left.readonly == right.readonly
                    && self.compare(left.constraint, right.constraint)
                    && self.optional_types_are_identical(left.name_type, right.name_type)
                    && self.compare(left.template, right.template)
            }
            _ => false,
        };
        self.active.pop();
        identical
    }

    fn types_are_identical(&mut self, left: &[Ty<'a>], right: &[Ty<'a>]) -> bool {
        left.len() == right.len()
            && left
                .iter()
                .zip(right)
                .all(|(left, right)| self.compare(*left, *right))
    }

    fn optional_types_are_identical(
        &mut self,
        left: Option<Ty<'a>>,
        right: Option<Ty<'a>>,
    ) -> bool {
        match (left, right) {
            (Some(left), Some(right)) => self.compare(left, right),
            (None, None) => true,
            _ => false,
        }
    }

    fn objects_are_identical(&mut self, left: &TyObject<'a>, right: &TyObject<'a>) -> bool {
        self.properties_are_identical(&left.properties, &right.properties)
            && left.signatures.len() == right.signatures.len()
            && left
                .signatures
                .iter()
                .zip(&right.signatures)
                .all(|(left, right)| left.kind == right.kind && self.compare(left.ty, right.ty))
            && left.index_infos.len() == right.index_infos.len()
            && left
                .index_infos
                .iter()
                .zip(&right.index_infos)
                .all(|(left, right)| {
                    left.name == right.name
                        && left.readonly == right.readonly
                        && self.compare(left.key_type, right.key_type)
                        && self.compare(left.value_type, right.value_type)
                })
    }

    fn properties_are_identical(
        &mut self,
        left: &[TyProperty<'a>],
        right: &[TyProperty<'a>],
    ) -> bool {
        left.len() == right.len()
            && left.iter().zip(right).all(|(left, right)| {
                left.name == right.name
                    && left.computed == right.computed
                    && left.optional == right.optional
                    && left.method == right.method
                    && left.readonly == right.readonly
                    && self.compare(left.ty, right.ty)
            })
    }

    fn functions_are_identical(&mut self, left: &TyFunction<'a>, right: &TyFunction<'a>) -> bool {
        left.type_parameters.len() == right.type_parameters.len()
            && left
                .type_parameters
                .iter()
                .zip(&right.type_parameters)
                .all(|(left, right)| self.type_parameters_are_identical(left, right))
            && left.parameters.len() == right.parameters.len()
            && left
                .parameters
                .iter()
                .zip(&right.parameters)
                .all(|(left, right)| {
                    left.name == right.name
                        && left.optional == right.optional
                        && left.rest == right.rest
                        && self.compare(left.ty, right.ty)
                })
            && self.compare(left.return_type, right.return_type)
            && match (left.type_predicate, right.type_predicate) {
                (Some(left), Some(right)) => self.type_predicates_are_identical(left, right),
                (None, None) => true,
                _ => false,
            }
    }

    fn type_parameters_are_identical(
        &mut self,
        left: &TyTypeParameter<'a>,
        right: &TyTypeParameter<'a>,
    ) -> bool {
        left.name == right.name
            && left.display_default == right.display_default
            && self.optional_types_are_identical(left.constraint_type, right.constraint_type)
            && self.optional_types_are_identical(left.default_type, right.default_type)
    }

    fn type_predicates_are_identical(
        &mut self,
        left: &TyTypePredicate<'a>,
        right: &TyTypePredicate<'a>,
    ) -> bool {
        left.kind == right.kind
            && left.parameter_name == right.parameter_name
            && left.parameter_index == right.parameter_index
            && self.optional_types_are_identical(left.target_type, right.target_type)
    }

    fn tuple_elements_are_identical(
        &mut self,
        left: &TupleElement<'a>,
        right: &TupleElement<'a>,
    ) -> bool {
        match (left, right) {
            (TupleElement::Regular(left), TupleElement::Regular(right))
            | (TupleElement::Rest(left), TupleElement::Rest(right))
            | (TupleElement::Optional(left), TupleElement::Optional(right)) => {
                self.compare(*left, *right)
            }
            _ => false,
        }
    }
}

// TODO: Allow early return so we don't visit unnecessary nodes
pub(crate) fn visit_type<'a>(arena: CheckerArena<'a>, ty: Ty<'a>, f: &mut impl FnMut(Ty<'a>)) {
    visit_type_at_depth(arena, ty, f, 0);
}

fn visit_type_at_depth<'a>(
    arena: CheckerArena<'a>,
    ty: Ty<'a>,
    f: &mut impl FnMut(Ty<'a>),
    depth: usize,
) {
    if depth >= TYPE_VISIT_MAX_DEPTH {
        return;
    }

    f(ty);
    let next_depth = depth + 1;
    match arena.type_data(ty) {
        TypeData::Object(object) => {
            for property in &object.properties {
                visit_type_at_depth(arena, property.ty, f, next_depth);
            }
            for signature in &object.signatures {
                visit_type_at_depth(arena, signature.ty, f, next_depth);
            }
            for info in &object.index_infos {
                visit_type_at_depth(arena, info.key_type, f, next_depth);
                visit_type_at_depth(arena, info.value_type, f, next_depth);
            }
        }
        TypeData::ModuleNamespace(namespace) => {
            for property in &namespace.properties {
                visit_type_at_depth(arena, property.ty, f, next_depth);
            }
        }
        TypeData::Function(function) => {
            for type_parameter in &function.type_parameters {
                if let Some(constraint_type) = type_parameter.constraint_type {
                    visit_type_at_depth(arena, constraint_type, f, next_depth);
                }
                if let Some(default_type) = type_parameter.default_type {
                    visit_type_at_depth(arena, default_type, f, next_depth);
                }
            }
            for parameter in &function.parameters {
                visit_type_at_depth(arena, parameter.ty, f, next_depth);
            }
            visit_type_at_depth(arena, function.return_type, f, next_depth);
            if let Some(target_type) = function
                .type_predicate
                .and_then(|predicate| predicate.target_type)
            {
                visit_type_at_depth(arena, target_type, f, next_depth);
            }
        }
        TypeData::TypeReference(reference) => {
            for ty in &reference.type_arguments {
                visit_type_at_depth(arena, *ty, f, next_depth);
            }
        }
        TypeData::TypeQuery(query) => {
            visit_type_at_depth(arena, query.resolved, f, next_depth);
            for ty in &query.type_arguments {
                visit_type_at_depth(arena, *ty, f, next_depth);
            }
        }
        TypeData::TemplateLiteral(template_literal) => {
            for ty in &template_literal.expressions {
                visit_type_at_depth(arena, *ty, f, next_depth);
            }
        }
        TypeData::Array(array) => {
            visit_type_at_depth(arena, array.element_type, f, next_depth);
        }
        TypeData::Tuple(tuple) => {
            for element in &tuple.elements {
                visit_type_at_depth(arena, element.ty(), f, next_depth);
            }
        }
        TypeData::Union(union) => {
            for ty in &union.types {
                visit_type_at_depth(arena, *ty, f, next_depth);
            }
        }
        TypeData::Intersection(intersection) => {
            for ty in &intersection.types {
                visit_type_at_depth(arena, *ty, f, next_depth);
            }
        }
        TypeData::Keyof(keyof) => visit_type_at_depth(arena, keyof.target, f, next_depth),
        TypeData::IndexedAccess(indexed_access) => {
            visit_type_at_depth(arena, indexed_access.object_type, f, next_depth);
            visit_type_at_depth(arena, indexed_access.index_type, f, next_depth);
        }
        TypeData::Conditional(conditional) => {
            visit_type_at_depth(arena, conditional.check_type, f, next_depth);
            visit_type_at_depth(arena, conditional.extends_type, f, next_depth);
            visit_type_at_depth(arena, conditional.true_type, f, next_depth);
            visit_type_at_depth(arena, conditional.false_type, f, next_depth);
        }
        TypeData::Infer(infer) => {
            if let Some(constraint_type) = infer.type_parameter.constraint_type {
                visit_type_at_depth(arena, constraint_type, f, next_depth);
            }
            if let Some(default_type) = infer.type_parameter.default_type {
                visit_type_at_depth(arena, default_type, f, next_depth);
            }
        }
        TypeData::Mapped(mapped) => {
            visit_type_at_depth(arena, mapped.constraint, f, next_depth);
            if let Some(name_type) = mapped.name_type {
                visit_type_at_depth(arena, name_type, f, next_depth);
            }
            visit_type_at_depth(arena, mapped.template, f, next_depth);
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
        arena.alloc_type(TypeData::NumberLiteral(arena.alloc(TyNumberLiteral {
            value,
            raw: Some(*arena.alloc(Str::from(raw))),
            base,
        })))
    }

    pub fn number_literal_from_ast(
        arena: CheckerArena<'a>,
        lit: &'a oxc_ast::ast::NumericLiteral,
        negated: bool,
    ) -> Self {
        // TODO: Do we need to store `-` in the raw string?
        let value = if negated { -lit.value } else { lit.value };
        arena.alloc_type(TypeData::NumberLiteral(arena.alloc(TyNumberLiteral {
            value,
            raw: lit.raw,
            base: lit.base,
        })))
    }

    pub fn string() -> Self {
        Self::String
    }

    pub fn symbol() -> Self {
        Self::Symbol
    }

    pub fn unique_symbol(arena: CheckerArena<'a>, name: Option<&'a str>) -> Self {
        arena.alloc_type(TypeData::UniqueSymbol(arena.alloc(TyUniqueSymbol { name })))
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
        Self::BOOLEAN_TRUE
    }

    /// Literal `false` type (subtype of `boolean`)
    pub fn boolean_false() -> Self {
        Self::BOOLEAN_FALSE
    }

    pub fn bigint() -> Self {
        Self::Bigint
    }

    pub fn bigint_literal(arena: CheckerArena<'a>, name: &'a str) -> Self {
        arena.alloc_type(TypeData::BigIntLiteral(
            arena.alloc(TyBigIntLiteral { value: name }),
        ))
    }

    pub fn template_literal(
        arena: CheckerArena<'a>,
        quasis: impl IntoIterator<Item = TemplateLiteralElement<'a>>,
        expressions: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        arena.alloc_type(TypeData::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter(quasis),
            expressions: arena.vec_from_iter(expressions),
        })))
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
        arena.alloc_type(TypeData::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(properties),
            signatures: arena.vec_from_iter(signatures),
            index_infos: arena.vec_from_iter(index_infos),
        })))
    }

    pub fn module_namespace(
        arena: CheckerArena<'a>,
        name: &'a str,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
    ) -> Self {
        arena.alloc_type(TypeData::ModuleNamespace(arena.alloc(TyModuleNamespace {
            name,
            properties: arena.vec_from_iter(properties),
        })))
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
        arena.alloc_type(TypeData::Function(arena.alloc(TyFunction {
            type_parameters: arena.vec_from_iter(type_parameters),
            parameters: arena.vec_from_iter(parameters),
            return_type,
            type_predicate: type_predicate.map(|predicate| arena.alloc(predicate)),
        })))
    }

    pub fn type_reference(
        arena: CheckerArena<'a>,
        name: &'a str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        let type_arguments = arena.vec_from_iter(type_arguments);
        let display_type_argument_count = type_arguments.len();
        arena.alloc_type(TypeData::TypeReference(arena.alloc(TyTypeReference {
            name,
            type_arguments,
            display_type_argument_count,
        })))
    }

    pub(crate) fn type_reference_with_display_type_argument_count(
        arena: CheckerArena<'a>,
        name: &'a str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
        display_type_argument_count: usize,
    ) -> Self {
        let type_arguments = arena.vec_from_iter(type_arguments);
        let display_type_argument_count = display_type_argument_count.min(type_arguments.len());
        arena.alloc_type(TypeData::TypeReference(arena.alloc(TyTypeReference {
            name,
            type_arguments,
            display_type_argument_count,
        })))
    }

    pub fn type_query(
        arena: CheckerArena<'a>,
        name: &'a str,
        resolved: Ty<'a>,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        arena.alloc_type(TypeData::TypeQuery(arena.alloc(TyTypeQuery {
            name,
            resolved,
            type_arguments: arena.vec_from_iter(type_arguments),
        })))
    }

    pub fn string_literal(arena: CheckerArena<'a>, value: &'a str) -> Self {
        arena.alloc_type(TypeData::StringLiteral(
            arena.alloc(TyStringLiteral { value }),
        ))
    }

    pub fn array(arena: CheckerArena<'a>, element_type: Ty<'a>) -> Self {
        arena.alloc_type(TypeData::Array(arena.alloc(TyArray {
            element_type,
            readonly: false,
            display_as_generic: false,
        })))
    }

    pub fn readonly_array(arena: CheckerArena<'a>, element_type: Ty<'a>) -> Self {
        arena.alloc_type(TypeData::Array(arena.alloc(TyArray {
            element_type,
            readonly: true,
            display_as_generic: false,
        })))
    }

    pub fn generic_array(arena: CheckerArena<'a>, element_type: Ty<'a>, readonly: bool) -> Self {
        arena.alloc_type(TypeData::Array(arena.alloc(TyArray {
            element_type,
            readonly,
            display_as_generic: true,
        })))
    }

    pub fn tuple(arena: CheckerArena<'a>, elements: Vec<TupleElement<'a>>) -> Self {
        arena.alloc_type(TypeData::Tuple(arena.alloc(TyTuple {
            elements: arena.vec_from_iter(elements),
            readonly: false,
        })))
    }

    pub fn readonly_tuple(arena: CheckerArena<'a>, elements: Vec<TupleElement<'a>>) -> Self {
        arena.alloc_type(TypeData::Tuple(arena.alloc(TyTuple {
            elements: arena.vec_from_iter(elements),
            readonly: true,
        })))
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
        arena.alloc_type(TypeData::Keyof(arena.alloc(TyKeyof { target })))
    }

    pub fn indexed_access(
        arena: CheckerArena<'a>,
        object_type: Ty<'a>,
        index_type: Ty<'a>,
    ) -> Self {
        arena.alloc_type(TypeData::IndexedAccess(arena.alloc(TyIndexedAccess {
            object_type,
            index_type,
        })))
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
        arena.alloc_type(TypeData::Infer(arena.alloc(TyInfer { type_parameter })))
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
        arena.alloc_type(TypeData::Mapped(arena.alloc(TyMapped {
            key,
            constraint,
            name_type,
            template,
            optional,
            readonly,
        })))
    }

    /// Returns `true` if the type is `none`, indicating that we have no information about this type.
    /// This is normally a bug and should be investigated.
    pub fn is_none(&self) -> bool {
        *self == Self::None
    }

    /// Returns `true` if the type is `any`.
    pub fn is_any(&self) -> bool {
        *self == Self::Any
    }

    /// Returns `true` if the type is `never`.
    pub fn is_never(&self) -> bool {
        *self == Self::Never
    }

    /// Returns `true` if the type is `undefined`.
    pub fn is_undefined(&self) -> bool {
        *self == Self::Undefined
    }

    pub(crate) fn is_transparent_type_alias_union_constituent(
        &self,
        arena: CheckerArena<'a>,
    ) -> bool {
        matches!(
            arena.type_data(*self),
            TypeData::String
                | TypeData::Number
                | TypeData::Boolean
                | TypeData::Bigint
                | TypeData::Symbol
                | TypeData::Undefined
                | TypeData::Null
                | TypeData::Void
                | TypeData::Never
                | TypeData::Any
                | TypeData::Unknown
                | TypeData::PrimitiveObject
                | TypeData::StringLiteral(_)
                | TypeData::NumberLiteral(_)
                | TypeData::BooleanLiteral(_)
                | TypeData::BigIntLiteral(_)
                | TypeData::TemplateLiteral(_)
                | TypeData::UniqueSymbol(_)
        )
    }

    /// Returns `true` if the type is a numerical index type.
    pub fn is_number_index_type(&self, arena: CheckerArena<'a>) -> bool {
        matches!(
            arena.type_data(*self),
            TypeData::Number | TypeData::NumberLiteral(_)
        )
    }

    pub fn enum_variant_name(self, arena: CheckerArena<'a>) -> &'static str {
        match arena.type_data(self) {
            TypeData::None => "TyNone",
            TypeData::Number => "TyNumber",
            TypeData::String => "TyString",
            TypeData::Boolean => "TyBoolean",
            TypeData::Bigint => "TyBigint",
            TypeData::Symbol => "TySymbol",
            TypeData::UniqueSymbol(_) => "TyUniqueSymbol",
            TypeData::Undefined => "TyUndefined",
            TypeData::Null => "TyNull",
            TypeData::Any => "TyAny",
            TypeData::Unknown => "TyUnknown",
            TypeData::Void => "TyVoid",
            TypeData::Never => "TyNever",
            TypeData::Object(_) => "TyObject",
            TypeData::ModuleNamespace(_) => "TyModuleNamespace",
            TypeData::PrimitiveObject => "TyPrimitiveObject",
            TypeData::This => "TyThis",
            TypeData::Function(_) => "TyFunction",
            TypeData::TypeReference(_) => "TyTypeReference",
            TypeData::TypeQuery(_) => "TyTypeQuery",
            TypeData::StringLiteral(_) => "TyStringLiteral",
            TypeData::NumberLiteral(_) => "TyNumberLiteral",
            TypeData::BooleanLiteral(_) => "TyBooleanLiteral",
            TypeData::BigIntLiteral(_) => "TyBigIntLiteral",
            TypeData::TemplateLiteral(_) => "TyTemplateLiteral",
            TypeData::Array(_) => "TyArray",
            TypeData::Tuple(_) => "TyTuple",
            TypeData::Union(_) => "TyUnion",
            TypeData::Intersection(_) => "TyIntersection",
            TypeData::Keyof(_) => "TyKeyof",
            TypeData::IndexedAccess(_) => "TyIndexedAccess",
            TypeData::Conditional(_) => "TyConditional",
            TypeData::Infer(_) => "TyInfer",
            TypeData::Mapped(_) => "TyMapped",
        }
    }

    #[allow(dead_code)]
    pub(crate) fn to_type_string(self, arena: CheckerArena<'a>) -> String {
        self.to_type_string_with(arena, &|_| None)
    }

    pub(crate) fn to_type_string_with(
        self,
        arena: CheckerArena<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
    ) -> String {
        let depth = Cell::new(0);
        self.to_type_string_with_depth(arena, replace_type_reference, &depth)
    }

    pub(crate) fn to_type_string_with_depth(
        self,
        arena: CheckerArena<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        depth: &Cell<usize>,
    ) -> String {
        self.to_type_string_with_flags(arena, replace_type_reference, TypeFormatFlags::NONE, depth)
    }

    fn to_type_string_with_flags(
        self,
        arena: CheckerArena<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let current = depth.get();
        if current >= TYPE_STRING_MAX_DEPTH {
            return "...".to_string();
        }

        depth.set(current + 1);
        let result = self.to_type_string_inner(arena, replace_type_reference, flags, depth);
        depth.set(current);
        result
    }

    fn to_type_string_inner(
        self,
        arena: CheckerArena<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        match arena.type_data(self) {
            TypeData::None => "none".to_string(),
            TypeData::Number => "number".to_string(),
            TypeData::String => "string".to_string(),
            TypeData::Boolean => "boolean".to_string(),
            TypeData::Bigint => "bigint".to_string(),
            TypeData::Symbol => "symbol".to_string(),
            TypeData::UniqueSymbol(unique_symbol) => unique_symbol.name.map_or_else(
                || "unique symbol".to_string(),
                |name| format!("typeof {name}"),
            ),
            TypeData::Undefined => "undefined".to_string(),
            TypeData::Null => "null".to_string(),
            TypeData::Any => "any".to_string(),
            TypeData::Unknown => "unknown".to_string(),
            TypeData::Void => "void".to_string(),
            TypeData::Never => "never".to_string(),
            TypeData::PrimitiveObject => "object".to_string(),
            TypeData::This => "this".to_string(),
            TypeData::Object(object) => {
                if object.properties.is_empty()
                    && object.signatures.is_empty()
                    && object.index_infos.is_empty()
                {
                    return "{}".to_string();
                }

                let members = object
                    .signatures
                    .iter()
                    .map(|signature| {
                        signature.to_type_string_with_flags(arena, &|_| None, flags, depth)
                    })
                    .chain(object.index_infos.iter().map(|info| {
                        let readonly = if info.readonly { "readonly " } else { "" };
                        format!(
                            "{}[{}: {}]: {};",
                            readonly,
                            info.name,
                            info.key_type.to_type_string_with_flags(
                                arena,
                                replace_type_reference,
                                flags,
                                depth,
                            ),
                            info.value_type.to_type_string_with_flags(
                                arena,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        )
                    }))
                    .chain(object.properties.iter().map(|property| {
                        let readonly = if property.readonly { "readonly " } else { "" };
                        if property.method
                            && let TypeData::Function(function) = arena.type_data(property.ty)
                        {
                            format!(
                                "{}{}{};",
                                readonly,
                                property_name_to_type_string(property),
                                signature_to_type_string(arena, function, &|_| None, flags, depth,)
                            )
                        } else {
                            format!(
                                "{}{}: {};",
                                readonly,
                                property_name_to_type_string(property),
                                property.ty.to_type_string_with_flags(
                                    arena,
                                    replace_type_reference,
                                    flags | TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE,
                                    depth,
                                )
                            )
                        }
                    }))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("{{ {members} }}")
            }
            TypeData::ModuleNamespace(namespace) => format!("typeof {}", namespace.name),
            TypeData::Function(function) => {
                function_type_to_string(arena, function, &|_| None, flags, depth)
            }
            TypeData::TypeReference(reference) => {
                if let Some(replacement) = replace_type_reference(self)
                    && replacement != self
                {
                    return replacement.to_type_string_with_flags(
                        arena,
                        replace_type_reference,
                        flags,
                        depth,
                    );
                }
                if reference.display_type_argument_count == 0 {
                    reference.name.to_string()
                } else {
                    let type_arguments = reference
                        .type_arguments
                        .iter()
                        .take(reference.display_type_argument_count)
                        .map(|ty| {
                            ty.to_type_string_with_flags(
                                arena,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{type_arguments}>", reference.name)
                }
            }
            TypeData::TypeQuery(query) => {
                if query.type_arguments.is_empty() {
                    format!("typeof {}", query.name)
                } else {
                    let type_arguments = query
                        .type_arguments
                        .iter()
                        .map(|ty| {
                            ty.to_type_string_with_flags(
                                arena,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("typeof {}<{type_arguments}>", query.name)
                }
            }
            TypeData::StringLiteral(string_literal) => {
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
            TypeData::NumberLiteral(number_literal) => {
                // Print the base-10 representation of the number
                if number_literal.value.is_zero() {
                    // Treat +0 and -0 as the same when printing.
                    "0".to_string()
                } else {
                    number_literal.value.to_string()
                }
            }
            TypeData::BooleanLiteral(value) => value.to_string(),
            TypeData::BigIntLiteral(big_int_literal) => format!("{}n", big_int_literal.value),
            TypeData::TemplateLiteral(template_literal) => {
                let mut repr = String::from("`");

                for (index, quasi) in template_literal.quasis.iter().enumerate() {
                    repr.push_str(quasi.value);
                    if let Some(expression) = template_literal.expressions.get(index) {
                        repr.push_str("${");
                        repr.push_str(&expression.to_type_string_with_flags(
                            arena,
                            replace_type_reference,
                            flags,
                            depth,
                        ));
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
                        repr.push_str(&expression.to_type_string_with_flags(
                            arena,
                            replace_type_reference,
                            flags,
                            depth,
                        ));
                        repr.push('}');
                    }
                }

                repr.push('`');
                repr
            }
            TypeData::Array(array) => {
                let element_type = array.element_type.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags,
                    depth,
                );
                if array.display_as_generic
                    && flags.contains(TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE)
                {
                    let name = if array.readonly {
                        "ReadonlyArray"
                    } else {
                        "Array"
                    };
                    return format!("{name}<{element_type}>");
                }
                let body = if array.element_type.display_needs_parentheses(arena) {
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
            TypeData::Tuple(tuple) => {
                let elements = tuple
                    .elements
                    .iter()
                    .map(|element| match element {
                        TupleElement::Regular(ty) => ty.to_type_string_with_flags(
                            arena,
                            replace_type_reference,
                            flags,
                            depth,
                        ),
                        TupleElement::Rest(ty) => format!(
                            "...{}",
                            ty.to_type_string_with_flags(
                                arena,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        ),
                        TupleElement::Optional(ty) => {
                            let ty = ty.to_type_string_with_flags(
                                arena,
                                replace_type_reference,
                                flags,
                                depth,
                            );
                            if element_type_needs_parentheses(arena, element) {
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
            TypeData::Union(union) => union
                .types
                .iter()
                .map(|ty| {
                    let type_string =
                        ty.to_type_string_with_flags(arena, replace_type_reference, flags, depth);
                    if ty.display_needs_parentheses(arena) {
                        format!("({type_string})")
                    } else {
                        type_string
                    }
                })
                .collect::<Vec<_>>()
                .join(" | "),
            TypeData::Intersection(intersection) => intersection
                .types
                .iter()
                .map(|ty| {
                    let type_string =
                        ty.to_type_string_with_flags(arena, replace_type_reference, flags, depth);
                    if ty.display_needs_parentheses(arena) {
                        format!("({type_string})")
                    } else {
                        type_string
                    }
                })
                .collect::<Vec<_>>()
                .join(" & "),
            TypeData::Keyof(keyof) => {
                let target = keyof.target.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags,
                    depth,
                );
                if keyof.target.display_needs_parentheses(arena) {
                    format!("keyof ({target})")
                } else {
                    format!("keyof {target}")
                }
            }
            TypeData::IndexedAccess(indexed_access) => {
                let object_type = indexed_access.object_type.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags,
                    depth,
                );
                let index_type = indexed_access.index_type.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags,
                    depth,
                );
                if indexed_access.object_type.display_needs_parentheses(arena) {
                    format!("({object_type})[{index_type}]")
                } else {
                    format!("{object_type}[{index_type}]")
                }
            }
            TypeData::Conditional(conditional) => {
                let check_type = conditional.check_type.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags,
                    depth,
                );
                let extends_type = conditional.extends_type.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags,
                    depth,
                );
                let check_type = if conditional.check_type.display_needs_parentheses(arena) {
                    format!("({check_type})")
                } else {
                    check_type
                };
                let extends_type = if matches!(
                    arena.type_data(conditional.extends_type),
                    TypeData::Conditional(_)
                ) {
                    format!("({extends_type})")
                } else {
                    extends_type
                };
                format!(
                    "{check_type} extends {extends_type} ? {} : {}",
                    conditional.true_type.to_type_string_with_flags(
                        arena,
                        replace_type_reference,
                        flags,
                        depth,
                    ),
                    conditional.false_type.to_type_string_with_flags(
                        arena,
                        replace_type_reference,
                        flags,
                        depth,
                    )
                )
            }
            TypeData::Infer(infer) => format!(
                "infer {}",
                type_parameter_to_type_string(
                    arena,
                    &infer.type_parameter,
                    &|_| None,
                    flags,
                    depth,
                )
            ),
            TypeData::Mapped(mapped) => {
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
                s.push_str(&mapped.constraint.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags,
                    depth,
                ));
                if let Some(name_type) = mapped.name_type {
                    s.push_str(" as ");
                    s.push_str(&name_type.to_type_string_with_flags(
                        arena,
                        replace_type_reference,
                        flags,
                        depth,
                    ));
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
                s.push_str(&mapped.template.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags,
                    depth,
                ));
                s.push_str("; }");
                s
            }
        }
    }

    /// Whether this type needs parentheses when printed
    fn display_needs_parentheses(&self, arena: CheckerArena<'a>) -> bool {
        matches!(
            arena.type_data(*self),
            TypeData::Function(_)
                | TypeData::Union(_)
                | TypeData::Intersection(_)
                | TypeData::Conditional(_)
                | TypeData::Infer(_)
        )
    }

    pub(crate) fn with_signatures(
        self,
        arena: CheckerArena<'a>,
        signatures: impl IntoIterator<Item = Signature<'a>>,
    ) -> Self {
        let TypeData::Object(object) = arena.type_data(self) else {
            return self;
        };
        arena.alloc_type(TypeData::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(object.properties.iter().copied()),
            signatures: arena.vec_from_iter(signatures),
            index_infos: arena.vec_from_iter(object.index_infos.iter().copied()),
        })))
    }

    pub(crate) fn with_index_infos(
        self,
        arena: CheckerArena<'a>,
        index_infos: impl IntoIterator<Item = IndexInfo<'a>>,
    ) -> Self {
        let TypeData::Object(object) = arena.type_data(self) else {
            return self;
        };
        arena.alloc_type(TypeData::Object(arena.alloc(TyObject {
            properties: arena.vec_from_iter(object.properties.iter().copied()),
            signatures: arena.vec_from_iter(object.signatures.iter().copied()),
            index_infos: arena.vec_from_iter(index_infos),
        })))
    }

    /// Returns `true` if the type is an object with no properties or signatures and has index infos.
    pub fn is_index_signature_object(&self, arena: CheckerArena<'a>) -> bool {
        let TypeData::Object(object) = arena.type_data(*self) else {
            return false;
        };
        object.signatures.is_empty()
            && object.properties.is_empty()
            && !object.index_infos.is_empty()
    }

    /// Returns the index infos of the type, or `None` if the type is not an object with index infos.
    pub fn index_infos(&self, arena: CheckerArena<'a>) -> Option<&'a [IndexInfo<'a>]> {
        let TypeData::Object(object) = arena.type_data(*self) else {
            return None;
        };
        if object.index_infos.is_empty() {
            None
        } else {
            Some(&object.index_infos)
        }
    }

    /// Returns the element type of an array type, or `None` if the type is not an array.
    pub fn array_element_type(&self, arena: CheckerArena<'a>) -> Option<Self> {
        let TypeData::Array(array) = arena.type_data(*self) else {
            return None;
        };
        Some(array.element_type)
    }

    /// Returns the string value of the type (if applicable).
    pub fn string_value(&self, arena: CheckerArena<'a>) -> Option<&'a str> {
        match arena.type_data(*self) {
            // Remove quoting
            TypeData::StringLiteral(string_literal) => Some(
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

    /// Returns the type, unioned with `undefined`.
    pub fn or_undefined(&self, arena: CheckerArena<'a>) -> Self {
        if *self == Ty::Undefined {
            *self
        } else {
            Self::union(arena, [*self, Ty::Undefined])
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
    if let Some(is_equal) = simplify_type_equality_function_extends(arena, check_type, extends_type)
    {
        return if is_equal { true_type } else { false_type };
    }

    if contains_unresolved_type_variable(arena, check_type)
        || contains_unresolved_type_variable(arena, extends_type)
        || contains_infer(arena, check_type)
        || contains_infer(arena, extends_type)
    {
        return arena.alloc_type(TypeData::Conditional(arena.alloc(TyConditional {
            check_type,
            extends_type,
            true_type,
            false_type,
            is_distributive,
        })));
    }

    if crate::relations::is_assignable_to_without_checker(arena, check_type, extends_type) {
        true_type
    } else {
        false_type
    }
}

fn simplify_type_equality_function_extends<'a>(
    arena: CheckerArena<'a>,
    check_type: Ty<'a>,
    extends_type: Ty<'a>,
) -> Option<bool> {
    let (TypeData::Function(check_function), TypeData::Function(extends_function)) =
        (arena.type_data(check_type), arena.type_data(extends_type))
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

    let TypeData::Conditional(check_return) = arena.type_data(check_function.return_type) else {
        return None;
    };
    let TypeData::Conditional(extends_return) = arena.type_data(extends_function.return_type)
    else {
        return None;
    };
    if contains_unresolved_type_variable(arena, check_return.extends_type)
        || contains_unresolved_type_variable(arena, extends_return.extends_type)
    {
        return None;
    }

    Some(
        crate::relations::is_assignable_to_without_checker(
            arena,
            check_return.extends_type,
            extends_return.extends_type,
        ) && crate::relations::is_assignable_to_without_checker(
            arena,
            extends_return.extends_type,
            check_return.extends_type,
        ),
    )
}

fn contains_unresolved_type_variable<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> bool {
    let mut contains = false;
    visit_type(arena, ty, &mut |ty| match arena.type_data(ty) {
        TypeData::TypeReference(reference) if reference.type_arguments.is_empty() => {
            contains = true;
        }
        TypeData::Function(function) if !function.type_parameters.is_empty() => contains = true,
        TypeData::Infer(_) => contains = true,
        _ => {}
    });
    contains
}

fn contains_infer<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> bool {
    let mut contains = false;
    visit_type(arena, ty, &mut |ty| {
        contains |= matches!(arena.type_data(ty), TypeData::Infer(_));
    });
    contains
}

fn element_type_needs_parentheses<'a>(arena: CheckerArena<'a>, element: &TupleElement<'a>) -> bool {
    match element {
        TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => {
            ty.display_needs_parentheses(arena)
        }
    }
}

fn type_parameter_to_type_string<'a>(
    arena: CheckerArena<'a>,
    type_parameter: &TyTypeParameter<'a>,
    replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
    flags: TypeFormatFlags,
    depth: &Cell<usize>,
) -> String {
    let mut type_string = type_parameter.name.to_string();
    if let Some(constraint_type) = type_parameter.constraint_type {
        type_string.push_str(" extends ");
        type_string.push_str(&constraint_type.to_type_string_with_flags(
            arena,
            replace_type_reference,
            flags,
            depth,
        ));
    }
    if type_parameter.display_default
        && let Some(default_type) = type_parameter.default_type
    {
        type_string.push_str(" = ");
        type_string.push_str(&default_type.to_type_string_with_flags(
            arena,
            replace_type_reference,
            flags,
            depth,
        ));
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
    pub(crate) ty: Ty<'a>,
}

impl<'a> Signature<'a> {
    pub(crate) fn new(kind: SignatureKind, ty: Ty<'a>) -> Self {
        Self { kind, ty }
    }

    pub(crate) fn function(self, arena: CheckerArena<'a>) -> &'a TyFunction<'a> {
        let TypeData::Function(function) = arena.type_data(self.ty) else {
            unreachable!("signature type must be a function")
        };
        function
    }

    fn to_type_string_with_flags(
        self,
        arena: CheckerArena<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let function = self.function(arena);
        match self.kind {
            SignatureKind::Call => format!(
                "{};",
                signature_to_type_string(arena, function, replace_type_reference, flags, depth,)
            ),
            SignatureKind::Construct => format!(
                "new {};",
                signature_to_type_string(arena, function, replace_type_reference, flags, depth,)
            ),
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

fn function_type_to_string<'a>(
    arena: CheckerArena<'a>,
    function: &TyFunction<'a>,
    replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
    flags: TypeFormatFlags,
    depth: &Cell<usize>,
) -> String {
    let (type_parameters, parameters) =
        function_type_head_to_string(arena, function, replace_type_reference, flags, depth);
    format!(
        "{type_parameters}({parameters}) => {}",
        function_return_type_to_string(arena, function, replace_type_reference, flags, depth)
    )
}

fn signature_to_type_string<'a>(
    arena: CheckerArena<'a>,
    function: &TyFunction<'a>,
    replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
    flags: TypeFormatFlags,
    depth: &Cell<usize>,
) -> String {
    let (type_parameters, parameters) =
        function_type_head_to_string(arena, function, replace_type_reference, flags, depth);
    format!(
        "{type_parameters}({parameters}): {}",
        function_return_type_to_string(arena, function, replace_type_reference, flags, depth)
    )
}

fn function_return_type_to_string<'a>(
    arena: CheckerArena<'a>,
    function: &TyFunction<'a>,
    replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
    flags: TypeFormatFlags,
    depth: &Cell<usize>,
) -> String {
    function.type_predicate.map_or_else(
        || {
            function.return_type.to_type_string_with_flags(
                arena,
                replace_type_reference,
                flags,
                depth,
            )
        },
        |predicate| {
            type_predicate_to_type_string(arena, predicate, replace_type_reference, flags, depth)
        },
    )
}

fn type_predicate_to_type_string<'a>(
    arena: CheckerArena<'a>,
    predicate: &TyTypePredicate<'a>,
    replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
    flags: TypeFormatFlags,
    depth: &Cell<usize>,
) -> String {
    let parameter_name = predicate.parameter_name.unwrap_or("this");
    let mut type_string = String::new();
    if predicate.kind.is_asserts() {
        type_string.push_str("asserts ");
    }
    type_string.push_str(parameter_name);
    if let Some(target_type) = predicate.target_type {
        type_string.push_str(" is ");
        type_string.push_str(&target_type.to_type_string_with_flags(
            arena,
            replace_type_reference,
            flags,
            depth,
        ));
    }
    type_string
}

fn function_type_head_to_string<'a>(
    arena: CheckerArena<'a>,
    function: &TyFunction<'a>,
    replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
    flags: TypeFormatFlags,
    depth: &Cell<usize>,
) -> (String, String) {
    let type_parameters = if function.type_parameters.is_empty() {
        String::new()
    } else {
        let type_parameters = function
            .type_parameters
            .iter()
            .map(|type_parameter| {
                type_parameter_to_type_string(
                    arena,
                    type_parameter,
                    replace_type_reference,
                    flags,
                    depth,
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("<{type_parameters}>")
    };
    let parameters = function
        .parameters
        .iter()
        .flat_map(|parameter| {
            function_parameter_to_type_strings(
                arena,
                parameter,
                replace_type_reference,
                flags,
                depth,
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    (type_parameters, parameters)
}

fn function_parameter_to_type_strings<'a>(
    arena: CheckerArena<'a>,
    parameter: &TyParameter<'a>,
    replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
    flags: TypeFormatFlags,
    depth: &Cell<usize>,
) -> Vec<String> {
    if parameter.rest
        && let TypeData::Tuple(tuple) = arena.type_data(parameter.ty)
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
                    TupleElement::Regular(ty) => format!(
                        "{name}: {}",
                        ty.to_type_string_with_flags(arena, replace_type_reference, flags, depth,)
                    ),
                    TupleElement::Optional(ty) => format!(
                        "{name}?: {}",
                        ty.to_type_string_with_flags(arena, replace_type_reference, flags, depth,)
                    ),
                    TupleElement::Rest(ty) => format!(
                        "...{name}: {}",
                        ty.to_type_string_with_flags(arena, replace_type_reference, flags, depth,)
                    ),
                }
            })
            .collect();
    }

    if parameter.rest {
        vec![format!(
            "...{}: {}",
            parameter.name,
            parameter
                .ty
                .to_type_string_with_flags(arena, replace_type_reference, flags, depth)
        )]
    } else if parameter.optional {
        vec![format!(
            "{}?: {}",
            parameter.name,
            parameter
                .ty
                .to_type_string_with_flags(arena, replace_type_reference, flags, depth)
        )]
    } else {
        vec![format!(
            "{}: {}",
            parameter.name,
            parameter
                .ty
                .to_type_string_with_flags(arena, replace_type_reference, flags, depth)
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
    use std::collections::HashMap;

    fn arena(allocator: &Allocator) -> CheckerArena<'_> {
        CheckerArena::new(allocator)
    }

    #[test]
    fn type_handles_are_compact() {
        assert_eq!(std::mem::size_of::<Ty<'_>>(), 4);
        assert_eq!(std::mem::size_of::<Option<Ty<'_>>>(), 4);
        assert_eq!(std::mem::size_of::<TypeId>(), 4);
    }

    #[test]
    fn type_identity_is_recursive_and_distinct_from_handle_identity() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let first = Ty::array(
            arena,
            Ty::object(arena, [Ty::property("value", Ty::string())]),
        );
        let second = Ty::array(
            arena,
            Ty::object(arena, [Ty::property("value", Ty::string())]),
        );
        let different = Ty::array(
            arena,
            Ty::object(arena, [Ty::property("value", Ty::number())]),
        );

        assert_ne!(first, second);
        assert!(arena.is_type_identical_to(first, second));
        assert!(!arena.is_type_identical_to(first, different));

        let mut by_id = HashMap::new();
        by_id.insert(first.id(), "first");
        by_id.insert(second.id(), "second");
        assert_eq!(by_id.len(), 2);
        assert_eq!(by_id[&first.id()], "first");
        assert_eq!(by_id[&second.id()], "second");
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

        let flattened = Ty::r#union(arena, [nested, Ty::number(), Ty::string()]);
        assert!(arena.is_type_identical_to(flattened, nested));
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
            Ty::r#union(arena, [Ty::number(), Ty::undefined()]).to_type_string(arena),
            "number | undefined"
        );
        assert_eq!(
            Ty::r#union(arena, [Ty::void(), Ty::undefined()]).to_type_string(arena),
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
        let literal_template =
            arena.alloc_type(TypeData::TemplateLiteral(arena.alloc(TyTemplateLiteral {
                quasis: arena.vec_from_iter([TemplateLiteralElement { value: "test" }]),
                expressions: arena.vec_from_iter([]),
            })));
        let pattern_template =
            arena.alloc_type(TypeData::TemplateLiteral(arena.alloc(TyTemplateLiteral {
                quasis: arena.vec_from_iter([
                    TemplateLiteralElement { value: "test" },
                    TemplateLiteralElement { value: "" },
                ]),
                expressions: arena.vec_from_iter([Ty::string()]),
            })));

        assert_eq!(
            Ty::r#union(arena, [literal_template, pattern_template]).to_type_string(arena),
            "`test${string}`"
        );
        assert_eq!(
            Ty::r#union(arena, [Ty::string_literal(arena, "test"), pattern_template])
                .to_type_string(arena),
            "`test${string}`"
        );

        let backtracking_template =
            arena.alloc_type(TypeData::TemplateLiteral(arena.alloc(TyTemplateLiteral {
                quasis: arena.vec_from_iter([
                    TemplateLiteralElement { value: "" },
                    TemplateLiteralElement { value: "a" },
                    TemplateLiteralElement { value: "" },
                ]),
                expressions: arena.vec_from_iter([Ty::string(), Ty::string_literal(arena, "b")]),
            })));
        assert_eq!(
            Ty::r#union(
                arena,
                [Ty::string_literal(arena, "aab"), backtracking_template]
            )
            .to_type_string(arena),
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
            Ty::r#union(arena, [function, Ty::null(), Ty::undefined()]).to_type_string(arena),
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
            Ty::object(arena, [abort]).to_type_string(arena),
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
            Ty::object(arena, [readonly]).to_type_string(arena),
            "{ readonly x: string; }"
        );
    }

    #[test]
    fn object_property_preserves_generic_array_declaration_syntax() {
        let allocator = Allocator::default();
        let arena = arena(&allocator);
        let array = Ty::generic_array(arena, Ty::string(), false);
        let values = TyProperty {
            name: "values",
            ty: array,
            computed: false,
            optional: true,
            method: false,
            readonly: false,
        };
        let maybe_values = TyProperty {
            name: "maybeValues",
            ty: Ty::union(arena, [array, Ty::undefined()]),
            computed: false,
            optional: false,
            method: false,
            readonly: false,
        };

        assert_eq!(array.to_type_string(arena), "string[]");
        assert_eq!(
            Ty::object(arena, [values, maybe_values]).to_type_string(arena),
            "{ values?: Array<string>; maybeValues: Array<string> | undefined; }"
        );
    }
}
