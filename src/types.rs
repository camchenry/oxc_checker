use crate::{
    checker::SymbolRef,
    limits::{TUPLE_SPREAD_MAX_LENGTH, TYPE_STRING_MAX_DEPTH, TYPE_VISIT_MAX_DEPTH},
    type_set::{reduce_intersection_type, reduce_source_union_type, reduce_union_type},
};
use bitflags::bitflags;
use num_traits::Zero;
use oxc_allocator::{Allocator, HashMap as ArenaHashMap, HashSet as ArenaHashSet, Vec as ArenaVec};
use oxc_ast::ast::{
    BigintBase, BindingPattern, NumberBase, PropertyKey, TSMappedTypeModifierOperator, TSType,
    TSTypeAnnotation, TSTypePredicate, TSTypePredicateName,
};
use oxc_index::Idx;
use oxc_str::Str;
use oxc_syntax::identifier::is_identifier_name;
use smallvec::SmallVec;
use std::{
    cell::{Cell, RefCell},
    marker::PhantomData,
    num::NonZeroU32,
};

const SYNTHETIC_INDEX_SIGNATURE_NAME: &str = "x";
const TYPE_VISIT_INLINE_WORDS: usize = 32;

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct TypeFormatFlags: u8 {
        const NONE = 0;
        const WRITE_ARRAY_AS_GENERIC_TYPE = 1 << 0;
        const PRESERVE_PROPERTY_NAME_QUOTES = 1 << 1;
        const USE_SINGLE_QUOTES_FOR_STRING_LITERAL = 1 << 2;
        const PARENTHESIZE_CONDITIONAL_RETURN = 1 << 3;
    }
}

#[derive(Clone, Copy)]
pub struct CheckerArena<'a> {
    allocator: &'a Allocator,
    types: &'a RefCell<ArenaVec<'a, TyKind<'a>>>,
    interned_types: &'a InternedTypeCache<'a>,
}

struct InternedTypeCache<'a> {
    strings: RefCell<ArenaHashMap<'a, &'a str, Ty<'a>>>,
    numbers: RefCell<ArenaHashMap<'a, u64, Ty<'a>>>,
    bigints: RefCell<ArenaHashMap<'a, &'a str, Ty<'a>>>,
    templates: RefCell<ArenaHashMap<'a, TemplateLiteralKey<'a>, Ty<'a>>>,
    arrays: RefCell<ArenaHashMap<'a, ArrayTypeKey, Ty<'a>>>,
    tuples: RefCell<ArenaHashMap<'a, TupleTypeKey<'a>, Ty<'a>>>,
    unions: RefCell<ArenaHashMap<'a, TypeListKey<'a>, Ty<'a>>>,
    intersections: RefCell<ArenaHashMap<'a, TypeListKey<'a>, Ty<'a>>>,
    keyofs: RefCell<ArenaHashMap<'a, TypeId, Ty<'a>>>,
    indexed_accesses: RefCell<ArenaHashMap<'a, (TypeId, TypeId), Ty<'a>>>,
    conditionals: RefCell<ArenaHashMap<'a, ConditionalTypeKey, Ty<'a>>>,
    type_references: RefCell<ArenaHashMap<'a, TypeReferenceKey<'a>, Ty<'a>>>,
    named_type_references: RefCell<ArenaHashMap<'a, NamedTypeReferenceKey<'a>, Ty<'a>>>,
    errors: RefCell<ArenaHashMap<'a, TypeErrorKind, Ty<'a>>>,
    fresh_object_literals: RefCell<ArenaHashSet<'a, TypeId>>,
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct TemplateLiteralKey<'a> {
    quasis: &'a [&'a str],
    expressions: &'a [TypeId],
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct ArrayTypeKey {
    element_type: TypeId,
    readonly: bool,
    display_as_generic: bool,
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct TupleTypeKey<'a> {
    elements: &'a [TupleElement<'a>],
    labels: Option<&'a [Option<&'a str>]>,
    readonly: bool,
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct TypeListKey<'a>(&'a [TypeId]);

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct ConditionalTypeKey {
    check_type: TypeId,
    extends_type: TypeId,
    true_type: TypeId,
    false_type: TypeId,
    is_distributive: bool,
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct TypeReferenceKey<'a> {
    target: SymbolRef,
    type_arguments: &'a [TypeId],
    display_type_argument_count: usize,
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct NamedTypeReferenceKey<'a> {
    name: &'a str,
    type_arguments: &'a [TypeId],
    display_type_argument_count: usize,
}

impl<'a> InternedTypeCache<'a> {
    fn new(allocator: &'a Allocator) -> Self {
        Self {
            strings: RefCell::new(ArenaHashMap::new_in(allocator)),
            numbers: RefCell::new(ArenaHashMap::new_in(allocator)),
            bigints: RefCell::new(ArenaHashMap::new_in(allocator)),
            templates: RefCell::new(ArenaHashMap::new_in(allocator)),
            arrays: RefCell::new(ArenaHashMap::new_in(allocator)),
            tuples: RefCell::new(ArenaHashMap::new_in(allocator)),
            unions: RefCell::new(ArenaHashMap::new_in(allocator)),
            intersections: RefCell::new(ArenaHashMap::new_in(allocator)),
            keyofs: RefCell::new(ArenaHashMap::new_in(allocator)),
            indexed_accesses: RefCell::new(ArenaHashMap::new_in(allocator)),
            conditionals: RefCell::new(ArenaHashMap::new_in(allocator)),
            type_references: RefCell::new(ArenaHashMap::new_in(allocator)),
            named_type_references: RefCell::new(ArenaHashMap::new_in(allocator)),
            errors: RefCell::new(ArenaHashMap::new_in(allocator)),
            fresh_object_literals: RefCell::new(ArenaHashSet::new_in(allocator)),
        }
    }
}

impl<'a> CheckerArena<'a> {
    pub fn new(allocator: &'a Allocator) -> Self {
        let types = allocator.alloc(RefCell::new(ArenaVec::new_in(&allocator)));
        let interned_types = allocator.alloc(InternedTypeCache::new(allocator));
        let arena = Self {
            allocator,
            types,
            interned_types,
        };
        {
            let mut types = arena.types.borrow_mut();
            for data in [
                TyKind::None,
                TyKind::Number,
                TyKind::String,
                TyKind::Boolean,
                TyKind::Bigint,
                TyKind::Symbol,
                TyKind::Undefined,
                TyKind::Null,
                TyKind::Any,
                TyKind::Unknown,
                TyKind::Void,
                TyKind::Never,
                TyKind::PrimitiveObject,
                TyKind::This,
                TyKind::BooleanLiteral(false),
                TyKind::BooleanLiteral(true),
                TyKind::GlobalThis,
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

    fn alloc_slice_copy<T: Copy>(&self, values: &[T]) -> &'a [T] {
        self.allocator.alloc_slice_copy(values)
    }

    pub(crate) fn alloc_slice_from_iter<T>(&self, values: impl IntoIterator<Item = T>) -> &'a [T] {
        self.vec_from_iter(values).into_arena_slice()
    }

    pub(crate) fn vec_from_iter<T>(&self, iter: impl IntoIterator<Item = T>) -> ArenaVec<'a, T> {
        ArenaVec::from_iter_in(iter, &self.allocator)
    }

    pub(crate) fn alloc_type(&self, data: TyKind<'a>) -> Ty<'a> {
        let mut types = self.types.borrow_mut();
        let ty = Ty::from_index(types.len());
        types.push(data);
        ty
    }

    pub(crate) fn is_fresh_object_literal(&self, ty: Ty<'a>) -> bool {
        self.interned_types
            .fresh_object_literals
            .borrow()
            .contains(&ty.id())
    }

    pub(crate) fn intern_union(&self, types: impl IntoIterator<Item = Ty<'a>>) -> Ty<'a> {
        self.intern_type_list(types, true)
    }

    pub(crate) fn intern_intersection(&self, types: Vec<Ty<'a>>) -> Ty<'a> {
        self.intern_type_list(types, false)
    }

    fn intern_conditional(
        &self,
        check_type: Ty<'a>,
        extends_type: Ty<'a>,
        true_type: Ty<'a>,
        false_type: Ty<'a>,
        is_distributive: bool,
    ) -> Ty<'a> {
        let key = ConditionalTypeKey {
            check_type: check_type.id(),
            extends_type: extends_type.id(),
            true_type: true_type.id(),
            false_type: false_type.id(),
            is_distributive,
        };
        if let Some(ty) = self.interned_types.conditionals.borrow().get(&key) {
            return *ty;
        }
        let ty = self.alloc_type(TyKind::Conditional(self.alloc(TyConditional {
            check_type,
            extends_type,
            true_type,
            false_type,
            is_distributive,
        })));
        self.interned_types
            .conditionals
            .borrow_mut()
            .insert(key, ty);
        ty
    }

    fn intern_type_list(&self, types: impl IntoIterator<Item = Ty<'a>>, union: bool) -> Ty<'a> {
        let types = types.into_iter().collect::<SmallVec<[_; 8]>>();
        let mut canonical_ids = types.iter().map(|ty| ty.id()).collect::<SmallVec<[_; 8]>>();
        if union {
            canonical_ids.sort_unstable();
        }
        let key = TypeListKey(&canonical_ids);
        let cache = if union {
            &self.interned_types.unions
        } else {
            &self.interned_types.intersections
        };
        if let Some(ty) = cache.borrow().get(&key) {
            return *ty;
        }
        let data = if union {
            TyKind::Union(self.alloc(TyUnion {
                types: self.vec_from_iter(types),
            }))
        } else {
            TyKind::Intersection(self.alloc(TyIntersection {
                types: self.vec_from_iter(types),
            }))
        };
        let ty = self.alloc_type(data);
        cache
            .borrow_mut()
            .insert(TypeListKey(self.alloc_slice_copy(&canonical_ids)), ty);
        ty
    }

    pub fn ty_kind(&self, ty: Ty<'a>) -> TyKind<'a> {
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
        // SAFETY: `Idx` requires callers to guarantee `index <= Self::MAX`.
        Self(unsafe { NonZeroU32::new_unchecked(index as u32 + 1) })
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeErrorKind {
    TypeInstantiationDepthExceeded,
    TypeResolutionDepthExceeded,
    ConditionalTypeDepthExceeded,
    TypeAliasResolutionDepthExceeded,
    UnresolvedImport,
    UnresolvedSymbol,
    UnresolvedMember,
    UnresolvedType,
    MissingGlobalType,
    MissingFunctionBody,
    TupleSizeExceeded,
    UnsupportedType,
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
        Self::from_id(TypeId::from_usize(index))
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
    const GLOBAL_THIS: Self = Self::from_raw(17);
}

#[repr(C, u8)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TyKind<'a> {
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
    Error(TypeErrorKind),
    Unknown,
    Void,
    Never,
    /// Primitive `object` keyword (not to be confused with `{}`)
    PrimitiveObject,
    This,
    /// Checker-owned global object whose properties are resolved lazily.
    GlobalThis,
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
    pub properties: &'a [TyProperty<'a>],
    members: Option<&'a TyObjectMembers<'a>>,
    pub is_constructor_type: bool,
}

#[derive(Debug, PartialEq, Eq)]
struct TyObjectMembers<'a> {
    signatures: &'a [Signature<'a>],
    index_infos: &'a [IndexInfo<'a>],
}

impl<'a> TyObject<'a> {
    /// Returns `true` if the object has no properties, signatures, or index infos.
    pub fn is_empty(&self) -> bool {
        self.properties.is_empty() && self.members.is_none()
    }

    pub fn signatures(&self) -> &'a [Signature<'a>] {
        self.members.map_or(&[], |members| members.signatures)
    }

    pub fn index_infos(&self) -> &'a [IndexInfo<'a>] {
        self.members.map_or(&[], |members| members.index_infos)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyModuleNamespace<'a> {
    pub name: &'a str,
    pub properties: ArenaVec<'a, TyProperty<'a>>,
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct TyPropertyFlags: u8 {
        const NONE = 0;
        const SINGLE_QUOTED = 1 << 0;
        const TYPE_SINGLE_QUOTED = 1 << 1;
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyProperty<'a> {
    pub name: &'a str,
    pub flags: TyPropertyFlags,
    pub ty: Ty<'a>,
    pub computed: bool,
    pub optional: bool,
    pub method: bool,
    pub readonly: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyFunction<'a> {
    pub type_parameters: ArenaVec<'a, TyTypeParameter<'a>>,
    /// Whether to render type parameters as instantiated type arguments.
    pub(crate) display_type_parameters_as_arguments: bool,
    pub parameters: ArenaVec<'a, TyParameter<'a>>,
    pub return_type: Ty<'a>,
    pub type_predicate: Option<&'a TyTypePredicate<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TyTypePredicateKind {
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
    pub kind: TyTypePredicateKind,
    pub parameter_name: Option<&'a str>,
    pub parameter_index: Option<usize>,
    pub target_type: Option<Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyTypeParameter<'a> {
    pub name: &'a str,
    /// constraint type (e.g., `U` in `T extends U`)
    pub constraint_type: Option<Ty<'a>>,
    pub default_type: Option<Ty<'a>>,
    // TODO: This should probably be a flag.
    /// Whether to display the default type when printing. This can be used to
    /// omit the default type in lib declarations.
    pub(crate) display_default: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyParameter<'a> {
    pub name: &'a str,
    pub ty: Ty<'a>,
    pub optional: bool,
    pub rest: bool,
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
    let TyKind::Tuple(tuple) = arena.ty_kind(ty) else {
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
    let TyKind::Tuple(tuple) = arena.ty_kind(ty) else {
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
    let TyKind::Tuple(tuple) = arena.ty_kind(ty) else {
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
    pub name: &'a str,
    pub target: Option<SymbolRef>,
    pub type_arguments: ArenaVec<'a, Ty<'a>>,
    pub(crate) display_type_argument_count: usize,
}

impl TyTypeReference<'_> {
    /// Returns `true` if the reference has no type arguments.
    pub fn is_bare(&self) -> bool {
        self.type_arguments.is_empty()
    }

    pub(crate) fn has_identical_target(&self, other: &Self) -> bool {
        match (self.target, other.target) {
            (Some(left), Some(right)) => left == right,
            _ => self.name == other.name,
        }
    }
}

impl PartialEq for TyTypeReference<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.target == other.target
            && self.type_arguments == other.type_arguments
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyTypeQuery<'a> {
    /// Display name of the queried entity (e.g. `"Foo"`, `"Foo.Bar"`, `"this"`).
    pub name: &'a str,
    /// The type of the queried symbol.
    pub resolved: Ty<'a>,
    /// Explicit type arguments on the query (e.g. `<U>` in `typeof Err<U>`).
    pub type_arguments: ArenaVec<'a, Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyStringLiteral<'a> {
    /// Decoded string contents without source quotes.
    pub value: &'a str,
}

#[derive(Debug, Clone, Copy)]
pub struct TyNumberLiteral<'a> {
    /// Value of the number literal, converted to base-10 floating point.
    pub value: f64,
    /// The number as it appears in source code
    ///
    /// Can be `None` if the number literal is not directly from the source code
    pub raw: Option<Str<'a>>,
    /// The base representation used by the literal in source code
    pub base: NumberBase,
}

impl PartialEq for TyNumberLiteral<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.value.total_cmp(&other.value) == std::cmp::Ordering::Equal
            && self.raw == other.raw
            && self.base == other.base
    }
}
impl Eq for TyNumberLiteral<'_> {}

fn canonical_number_literal_key(value: f64) -> u64 {
    if value == 0.0 {
        0.0f64.to_bits()
    } else {
        value.to_bits()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyBigIntLiteral<'a> {
    /// Value in base 10 without numeric separators.
    pub value: &'a str,
    /// The bigint as it appears in source code.
    pub raw: Option<Str<'a>>,
    /// The base representation used by the literal in source code.
    pub base: BigintBase,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TyUniqueSymbol<'a> {
    pub name: Option<&'a str>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyTemplateLiteral<'a> {
    pub quasis: ArenaVec<'a, TemplateLiteralElement<'a>>,
    pub expressions: ArenaVec<'a, Ty<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TemplateLiteralElement<'a> {
    pub value: &'a str,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyArray<'a> {
    pub element_type: Ty<'a>,
    /// `true` when produced from `readonly T[]` or `ReadonlyArray<T>`.
    pub readonly: bool,
    /// Whether to display this array using `Array<T>` or `ReadonlyArray<T>` syntax.
    pub(crate) display_as_generic: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyTuple<'a> {
    pub elements: ArenaVec<'a, TupleElement<'a>>,
    labels: Option<&'a [Option<&'a str>]>,
    /// `true` when produced from a `readonly` tuple literal.
    pub readonly: bool,
}

impl<'a> TyTuple<'a> {
    /// Returns the labels sidecar when at least one tuple element is labeled.
    pub fn labels(&self) -> Option<&[Option<&'a str>]> {
        self.labels
    }

    /// Returns this tuple's elements paired with their labels.
    pub fn labeled_elements(&self) -> impl Iterator<Item = LabeledTupleElement<'a>> + '_ {
        self.elements
            .iter()
            .copied()
            .enumerate()
            .map(|(index, element)| LabeledTupleElement {
                element,
                label: self.labels.and_then(|labels| labels[index]),
            })
    }

    pub fn element_type_at_index(&self, arena: CheckerArena<'a>, index: usize) -> Ty<'a> {
        let mut current_index = 0;
        for element in &self.elements {
            match element {
                TupleElement::Regular(ty) | TupleElement::Optional(ty) => {
                    if current_index == index {
                        return *ty;
                    }
                    current_index += 1;
                }
                TupleElement::Rest(ty) if index >= current_index => {
                    return ty.array_element_type(arena).unwrap_or(*ty);
                }
                TupleElement::Rest(_) => {}
            }
        }

        Ty::undefined()
    }
}

/// A tuple element is either: a regular type [`Ty`], a rest type, or an optional type.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
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
    pub fn ty(&self) -> Ty<'a> {
        match self {
            TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => *ty,
        }
    }

    /// Maps the type of this tuple element while preserving its kind.
    #[must_use]
    pub fn map_ty(self, f: impl FnOnce(Ty<'a>) -> Ty<'a>) -> Self {
        match self {
            TupleElement::Regular(ty) => TupleElement::Regular(f(ty)),
            TupleElement::Rest(ty) => TupleElement::Rest(f(ty)),
            TupleElement::Optional(ty) => TupleElement::Optional(f(ty)),
        }
    }
}

/// A tuple element paired with its optional source label.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct LabeledTupleElement<'a> {
    /// The element's type and regular, optional, or rest kind.
    pub element: TupleElement<'a>,
    /// The source label, or `None` for an unlabeled element.
    pub label: Option<&'a str>,
}

impl<'a> LabeledTupleElement<'a> {
    /// Creates a tuple element record with an optional source label.
    pub const fn new(element: TupleElement<'a>, label: Option<&'a str>) -> Self {
        Self { element, label }
    }

    /// Creates an unlabeled tuple element record.
    pub const fn unlabeled(element: TupleElement<'a>) -> Self {
        Self::new(element, None)
    }

    /// Maps the type while preserving the element kind and label.
    #[must_use]
    pub fn map_ty(self, f: impl FnOnce(Ty<'a>) -> Ty<'a>) -> Self {
        Self::new(self.element.map_ty(f), self.label)
    }
}

/// Whether a tuple constructed with labels is mutable or readonly.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TupleReadonly {
    /// A mutable tuple such as `[string]`.
    Mutable,
    /// A readonly tuple such as `readonly [string]`.
    Readonly,
}

impl TupleReadonly {
    pub(crate) const fn from_readonly(readonly: bool) -> Self {
        if readonly {
            Self::Readonly
        } else {
            Self::Mutable
        }
    }

    const fn is_readonly(self) -> bool {
        matches!(self, Self::Readonly)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyUnion<'a> {
    pub types: ArenaVec<'a, Ty<'a>>,
    // TODO: Add flags
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyIntersection<'a> {
    pub types: ArenaVec<'a, Ty<'a>>,
    // TODO: Add flags
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyKeyof<'a> {
    pub target: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyIndexedAccess<'a> {
    pub object_type: Ty<'a>,
    pub index_type: Ty<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyConditional<'a> {
    /// The type being checked
    pub check_type: Ty<'a>,
    /// The type that the check type extends
    pub extends_type: Ty<'a>,
    /// The type to use if the check is true
    pub true_type: Ty<'a>,
    /// The type to use if the check is false
    pub false_type: Ty<'a>,
    /// Whether the conditional type is distributive
    ///
    /// Example: `T extends U ? X : Y` is distributive if `T` is a union type.
    pub is_distributive: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyInfer<'a> {
    pub type_parameter: TyTypeParameter<'a>,
}

/// Mapped type, mirroring typescript-go's `MappedType` shape.
#[derive(Debug, PartialEq, Eq)]
pub struct TyMapped<'a> {
    /// Name of the key type parameter (the `P` in `[P in K]`).
    pub key: &'a str,
    /// Constraint of the key (the `K` in `[P in K]`).
    pub constraint: Ty<'a>,
    /// Optional `as N` key remapping type.
    pub name_type: Option<Ty<'a>>,
    /// Value type (right-hand side of the index signature).
    pub template: Ty<'a>,
    /// Optional modifier on the value (`?`, `+?`, `-?`).
    pub optional: MappedModifier,
    /// Readonly modifier on the index signature (`readonly`, `+readonly`, `-readonly`).
    pub readonly: MappedModifier,
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
    active: SmallVec<[(TypeId, TypeId); 8]>,
}

impl<'a> TypeIdentity<'a> {
    fn new(arena: CheckerArena<'a>) -> Self {
        Self {
            arena,
            active: SmallVec::new(),
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
        let identical = match (self.arena.ty_kind(left), self.arena.ty_kind(right)) {
            (TyKind::None, TyKind::None)
            | (TyKind::Number, TyKind::Number)
            | (TyKind::String, TyKind::String)
            | (TyKind::Boolean, TyKind::Boolean)
            | (TyKind::Bigint, TyKind::Bigint)
            | (TyKind::Symbol, TyKind::Symbol)
            | (TyKind::Undefined, TyKind::Undefined)
            | (TyKind::Null, TyKind::Null)
            | (TyKind::Any, TyKind::Any)
            | (TyKind::Unknown, TyKind::Unknown)
            | (TyKind::Void, TyKind::Void)
            | (TyKind::Never, TyKind::Never)
            | (TyKind::PrimitiveObject, TyKind::PrimitiveObject)
            | (TyKind::This, TyKind::This)
            | (TyKind::GlobalThis, TyKind::GlobalThis) => true,
            (TyKind::Error(left), TyKind::Error(right)) => left == right,
            (TyKind::UniqueSymbol(left), TyKind::UniqueSymbol(right)) => left == right,
            (TyKind::Object(left), TyKind::Object(right)) => {
                self.objects_are_identical(left, right)
            }
            (TyKind::ModuleNamespace(left), TyKind::ModuleNamespace(right)) => {
                left.name == right.name
                    && self.properties_are_identical(&left.properties, &right.properties)
            }
            (TyKind::Function(left), TyKind::Function(right)) => {
                self.functions_are_identical(left, right)
            }
            (TyKind::TypeReference(left), TyKind::TypeReference(right)) => {
                left.has_identical_target(right)
                    && self.types_are_identical(&left.type_arguments, &right.type_arguments)
            }
            (TyKind::TypeQuery(left), TyKind::TypeQuery(right)) => {
                left.name == right.name
                    && self.compare(left.resolved, right.resolved)
                    && self.types_are_identical(&left.type_arguments, &right.type_arguments)
            }
            (TyKind::StringLiteral(left), TyKind::StringLiteral(right)) => left == right,
            (TyKind::NumberLiteral(left), TyKind::NumberLiteral(right)) => left == right,
            (TyKind::BooleanLiteral(left), TyKind::BooleanLiteral(right)) => left == right,
            (TyKind::BigIntLiteral(left), TyKind::BigIntLiteral(right)) => left == right,
            (TyKind::TemplateLiteral(left), TyKind::TemplateLiteral(right)) => {
                left.quasis == right.quasis
                    && self.types_are_identical(&left.expressions, &right.expressions)
            }
            (TyKind::Array(left), TyKind::Array(right)) => {
                left.readonly == right.readonly
                    && self.compare(left.element_type, right.element_type)
            }
            (TyKind::Tuple(left), TyKind::Tuple(right)) => {
                left.readonly == right.readonly
                    && left.elements.len() == right.elements.len()
                    && left
                        .elements
                        .iter()
                        .zip(&right.elements)
                        .all(|(left, right)| self.tuple_elements_are_identical(left, right))
            }
            (TyKind::Union(left), TyKind::Union(right)) => {
                self.types_are_identical(&left.types, &right.types)
            }
            (TyKind::Intersection(left), TyKind::Intersection(right)) => {
                self.types_are_identical(&left.types, &right.types)
            }
            (TyKind::Keyof(left), TyKind::Keyof(right)) => self.compare(left.target, right.target),
            (TyKind::IndexedAccess(left), TyKind::IndexedAccess(right)) => {
                self.compare(left.object_type, right.object_type)
                    && self.compare(left.index_type, right.index_type)
            }
            (TyKind::Conditional(left), TyKind::Conditional(right)) => {
                left.is_distributive == right.is_distributive
                    && self.compare(left.check_type, right.check_type)
                    && self.compare(left.extends_type, right.extends_type)
                    && self.compare(left.true_type, right.true_type)
                    && self.compare(left.false_type, right.false_type)
            }
            (TyKind::Infer(left), TyKind::Infer(right)) => {
                self.type_parameters_are_identical(&left.type_parameter, &right.type_parameter)
            }
            (TyKind::Mapped(left), TyKind::Mapped(right)) => {
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
        self.properties_are_identical(left.properties, right.properties)
            && left.signatures().len() == right.signatures().len()
            && left
                .signatures()
                .iter()
                .zip(right.signatures())
                .all(|(left, right)| {
                    left.kind == right.kind
                        && left.is_abstract == right.is_abstract
                        && self.compare(left.ty, right.ty)
                })
            && left.index_infos().len() == right.index_infos().len()
            && left
                .index_infos()
                .iter()
                .zip(right.index_infos())
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

pub(crate) fn visit_type<'a>(arena: CheckerArena<'a>, ty: Ty<'a>, f: &mut impl FnMut(Ty<'a>)) {
    let mut visited = SmallVec::<[u64; TYPE_VISIT_INLINE_WORDS]>::new();
    visited.resize(arena.type_count().div_ceil(u64::BITS as usize), 0);
    visit_type_at_depth(arena, ty, f, &mut visited, 0);
}

fn visit_type_at_depth<'a>(
    arena: CheckerArena<'a>,
    ty: Ty<'a>,
    f: &mut impl FnMut(Ty<'a>),
    visited: &mut [u64],
    depth: usize,
) {
    let index = ty.id().index();
    let word = index / u64::BITS as usize;
    let mask = 1 << (index % u64::BITS as usize);
    if depth >= TYPE_VISIT_MAX_DEPTH || visited[word] & mask != 0 {
        return;
    }
    visited[word] |= mask;

    f(ty);
    let next_depth = depth + 1;
    match arena.ty_kind(ty) {
        TyKind::Object(object) => {
            for property in object.properties {
                visit_type_at_depth(arena, property.ty, f, visited, next_depth);
            }
            for signature in object.signatures() {
                visit_type_at_depth(arena, signature.ty, f, visited, next_depth);
            }
            for info in object.index_infos() {
                visit_type_at_depth(arena, info.key_type, f, visited, next_depth);
                visit_type_at_depth(arena, info.value_type, f, visited, next_depth);
            }
        }
        TyKind::ModuleNamespace(namespace) => {
            for property in &namespace.properties {
                visit_type_at_depth(arena, property.ty, f, visited, next_depth);
            }
        }
        TyKind::Function(function) => {
            for type_parameter in &function.type_parameters {
                if let Some(constraint_type) = type_parameter.constraint_type {
                    visit_type_at_depth(arena, constraint_type, f, visited, next_depth);
                }
                if let Some(default_type) = type_parameter.default_type {
                    visit_type_at_depth(arena, default_type, f, visited, next_depth);
                }
            }
            for parameter in &function.parameters {
                visit_type_at_depth(arena, parameter.ty, f, visited, next_depth);
            }
            visit_type_at_depth(arena, function.return_type, f, visited, next_depth);
            if let Some(target_type) = function
                .type_predicate
                .and_then(|predicate| predicate.target_type)
            {
                visit_type_at_depth(arena, target_type, f, visited, next_depth);
            }
        }
        TyKind::TypeReference(reference) => {
            for ty in &reference.type_arguments {
                visit_type_at_depth(arena, *ty, f, visited, next_depth);
            }
        }
        TyKind::TypeQuery(query) => {
            visit_type_at_depth(arena, query.resolved, f, visited, next_depth);
            for ty in &query.type_arguments {
                visit_type_at_depth(arena, *ty, f, visited, next_depth);
            }
        }
        TyKind::TemplateLiteral(template_literal) => {
            for ty in &template_literal.expressions {
                visit_type_at_depth(arena, *ty, f, visited, next_depth);
            }
        }
        TyKind::Array(array) => {
            visit_type_at_depth(arena, array.element_type, f, visited, next_depth);
        }
        TyKind::Tuple(tuple) => {
            for element in &tuple.elements {
                visit_type_at_depth(arena, element.ty(), f, visited, next_depth);
            }
        }
        TyKind::Union(union) => {
            for ty in &union.types {
                visit_type_at_depth(arena, *ty, f, visited, next_depth);
            }
        }
        TyKind::Intersection(intersection) => {
            for ty in &intersection.types {
                visit_type_at_depth(arena, *ty, f, visited, next_depth);
            }
        }
        TyKind::Keyof(keyof) => visit_type_at_depth(arena, keyof.target, f, visited, next_depth),
        TyKind::IndexedAccess(indexed_access) => {
            visit_type_at_depth(arena, indexed_access.object_type, f, visited, next_depth);
            visit_type_at_depth(arena, indexed_access.index_type, f, visited, next_depth);
        }
        TyKind::Conditional(conditional) => {
            visit_type_at_depth(arena, conditional.check_type, f, visited, next_depth);
            visit_type_at_depth(arena, conditional.extends_type, f, visited, next_depth);
            visit_type_at_depth(arena, conditional.true_type, f, visited, next_depth);
            visit_type_at_depth(arena, conditional.false_type, f, visited, next_depth);
        }
        TyKind::Infer(infer) => {
            if let Some(constraint_type) = infer.type_parameter.constraint_type {
                visit_type_at_depth(arena, constraint_type, f, visited, next_depth);
            }
            if let Some(default_type) = infer.type_parameter.default_type {
                visit_type_at_depth(arena, default_type, f, visited, next_depth);
            }
        }
        TyKind::Mapped(mapped) => {
            visit_type_at_depth(arena, mapped.constraint, f, visited, next_depth);
            if let Some(name_type) = mapped.name_type {
                visit_type_at_depth(arena, name_type, f, visited, next_depth);
            }
            visit_type_at_depth(arena, mapped.template, f, visited, next_depth);
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
        let key = canonical_number_literal_key(value);
        if let Some(ty) = arena.interned_types.numbers.borrow().get(&key) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::NumberLiteral(arena.alloc(TyNumberLiteral {
            value,
            raw: Some(*arena.alloc(Str::from(raw))),
            base,
        })));
        arena.interned_types.numbers.borrow_mut().insert(key, ty);
        ty
    }

    pub fn number_literal_from_ast(
        arena: CheckerArena<'a>,
        lit: &'a oxc_ast::ast::NumericLiteral,
        negated: bool,
    ) -> Self {
        // TODO: Do we need to store `-` in the raw string?
        let value = if negated { -lit.value } else { lit.value };
        let key = canonical_number_literal_key(value);
        if let Some(ty) = arena.interned_types.numbers.borrow().get(&key) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::NumberLiteral(arena.alloc(TyNumberLiteral {
            value,
            raw: lit.raw,
            base: lit.base,
        })));
        arena.interned_types.numbers.borrow_mut().insert(key, ty);
        ty
    }

    pub fn string() -> Self {
        Self::String
    }

    pub fn symbol() -> Self {
        Self::Symbol
    }

    pub fn unique_symbol(arena: CheckerArena<'a>, name: Option<&'a str>) -> Self {
        arena.alloc_type(TyKind::UniqueSymbol(arena.alloc(TyUniqueSymbol { name })))
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

    pub fn bigint_literal(
        arena: CheckerArena<'a>,
        value: &'a str,
        raw: Option<Str<'a>>,
        base: BigintBase,
    ) -> Self {
        if let Some(ty) = arena.interned_types.bigints.borrow().get(value) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::BigIntLiteral(arena.alloc(TyBigIntLiteral {
            value,
            raw,
            base,
        })));
        arena.interned_types.bigints.borrow_mut().insert(value, ty);
        ty
    }

    pub fn template_literal(
        arena: CheckerArena<'a>,
        quasis: impl IntoIterator<Item = TemplateLiteralElement<'a>>,
        expressions: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        let quasis = quasis.into_iter().collect::<Vec<_>>();
        let expressions = expressions.into_iter().collect::<Vec<_>>();
        let quasi_values = quasis.iter().map(|quasi| quasi.value).collect::<Vec<_>>();
        let expression_ids = expressions.iter().map(|ty| ty.id()).collect::<Vec<_>>();
        let key = TemplateLiteralKey {
            quasis: &quasi_values,
            expressions: &expression_ids,
        };
        if let Some(ty) = arena.interned_types.templates.borrow().get(&key) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::TemplateLiteral(arena.alloc(TyTemplateLiteral {
            quasis: arena.vec_from_iter(quasis),
            expressions: arena.vec_from_iter(expressions),
        })));
        arena.interned_types.templates.borrow_mut().insert(
            TemplateLiteralKey {
                quasis: arena.alloc_slice_copy(&quasi_values),
                expressions: arena.alloc_slice_copy(&expression_ids),
            },
            ty,
        );
        ty
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

    pub fn error(arena: CheckerArena<'a>, kind: TypeErrorKind) -> Self {
        if let Some(ty) = arena.interned_types.errors.borrow().get(&kind) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::Error(kind));
        arena.interned_types.errors.borrow_mut().insert(kind, ty);
        ty
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

    pub fn global_this() -> Self {
        Self::GLOBAL_THIS
    }

    pub fn property(name: &'a str, ty: Ty<'a>) -> TyProperty<'a> {
        TyProperty {
            name,
            flags: TyPropertyFlags::NONE,
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

    pub fn object_literal(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
    ) -> Self {
        let ty = Self::object(arena, properties);
        arena
            .interned_types
            .fresh_object_literals
            .borrow_mut()
            .insert(ty.id());
        ty
    }

    pub fn object_literal_with_index_infos(
        arena: CheckerArena<'a>,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
        index_infos: impl IntoIterator<Item = IndexInfo<'a>>,
    ) -> Self {
        let index_infos = index_infos.into_iter().collect::<Vec<_>>();
        if index_infos.is_empty() {
            return Self::object_literal(arena, properties);
        }
        let ty = Self::object_with_index_infos(arena, properties, index_infos);
        arena
            .interned_types
            .fresh_object_literals
            .borrow_mut()
            .insert(ty.id());
        ty
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

    pub fn constructor_type(arena: CheckerArena<'a>, signature: Signature<'a>) -> Self {
        Self::object_from_slices(
            arena,
            &[],
            arena.alloc_slice_from_iter([signature]),
            &[],
            true,
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
        Self::object_from_slices(
            arena,
            arena.alloc_slice_from_iter(properties),
            arena.alloc_slice_from_iter(signatures),
            arena.alloc_slice_from_iter(index_infos),
            false,
        )
    }

    pub(crate) fn object_from_slices(
        arena: CheckerArena<'a>,
        properties: &'a [TyProperty<'a>],
        signatures: &'a [Signature<'a>],
        index_infos: &'a [IndexInfo<'a>],
        is_constructor_type: bool,
    ) -> Self {
        let members = (!signatures.is_empty() || !index_infos.is_empty()).then(|| {
            arena.alloc(TyObjectMembers {
                signatures,
                index_infos,
            })
        });
        arena.alloc_type(TyKind::Object(arena.alloc(TyObject {
            properties,
            members,
            is_constructor_type,
        })))
    }

    pub fn module_namespace(
        arena: CheckerArena<'a>,
        name: &'a str,
        properties: impl IntoIterator<Item = TyProperty<'a>>,
    ) -> Self {
        arena.alloc_type(TyKind::ModuleNamespace(arena.alloc(TyModuleNamespace {
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
        Self::function_with_type_predicate_and_display(
            arena,
            type_parameters,
            parameters,
            return_type,
            type_predicate,
            false,
        )
    }

    pub(crate) fn function_with_type_predicate_and_display(
        arena: CheckerArena<'a>,
        type_parameters: impl IntoIterator<Item = TyTypeParameter<'a>>,
        parameters: impl IntoIterator<Item = TyParameter<'a>>,
        return_type: Ty<'a>,
        type_predicate: Option<TyTypePredicate<'a>>,
        display_type_parameters_as_arguments: bool,
    ) -> Self {
        arena.alloc_type(TyKind::Function(arena.alloc(TyFunction {
            type_parameters: arena.vec_from_iter(type_parameters),
            display_type_parameters_as_arguments,
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
        let type_arguments = type_arguments.into_iter().collect::<Vec<_>>();
        let display_type_argument_count = type_arguments.len();
        Self::intern_named_type_reference(arena, name, type_arguments, display_type_argument_count)
    }

    pub(crate) fn type_reference_with_display_type_argument_count(
        arena: CheckerArena<'a>,
        name: &'a str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
        display_type_argument_count: usize,
    ) -> Self {
        let type_arguments = type_arguments.into_iter().collect::<Vec<_>>();
        let display_type_argument_count = display_type_argument_count.min(type_arguments.len());
        Self::intern_named_type_reference(arena, name, type_arguments, display_type_argument_count)
    }

    fn intern_named_type_reference(
        arena: CheckerArena<'a>,
        name: &'a str,
        type_arguments: Vec<Ty<'a>>,
        display_type_argument_count: usize,
    ) -> Self {
        let type_argument_ids = type_arguments.iter().map(|ty| ty.id()).collect::<Vec<_>>();
        let key = NamedTypeReferenceKey {
            name,
            type_arguments: &type_argument_ids,
            display_type_argument_count,
        };
        if let Some(ty) = arena
            .interned_types
            .named_type_references
            .borrow()
            .get(&key)
        {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::TypeReference(arena.alloc(TyTypeReference {
            name,
            target: None,
            type_arguments: arena.vec_from_iter(type_arguments),
            display_type_argument_count,
        })));
        arena
            .interned_types
            .named_type_references
            .borrow_mut()
            .insert(
                NamedTypeReferenceKey {
                    name,
                    type_arguments: arena.alloc_slice_copy(&type_argument_ids),
                    display_type_argument_count,
                },
                ty,
            );
        ty
    }

    pub(crate) fn type_reference_for_symbol(
        arena: CheckerArena<'a>,
        name: &'a str,
        target: SymbolRef,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
        display_type_argument_count: usize,
    ) -> Self {
        let type_arguments = type_arguments.into_iter().collect::<Vec<_>>();
        let display_type_argument_count = display_type_argument_count.min(type_arguments.len());
        let type_argument_ids = type_arguments.iter().map(|ty| ty.id()).collect::<Vec<_>>();
        let key = TypeReferenceKey {
            target,
            type_arguments: &type_argument_ids,
            display_type_argument_count,
        };
        if let Some(ty) = arena.interned_types.type_references.borrow().get(&key) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::TypeReference(arena.alloc(TyTypeReference {
            name,
            target: Some(target),
            type_arguments: arena.vec_from_iter(type_arguments),
            display_type_argument_count,
        })));
        arena.interned_types.type_references.borrow_mut().insert(
            TypeReferenceKey {
                target,
                type_arguments: arena.alloc_slice_copy(&type_argument_ids),
                display_type_argument_count,
            },
            ty,
        );
        ty
    }

    pub fn type_query(
        arena: CheckerArena<'a>,
        name: &'a str,
        resolved: Ty<'a>,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        arena.alloc_type(TyKind::TypeQuery(arena.alloc(TyTypeQuery {
            name,
            resolved,
            type_arguments: arena.vec_from_iter(type_arguments),
        })))
    }

    pub fn string_literal(arena: CheckerArena<'a>, value: &'a str) -> Self {
        if let Some(ty) = arena.interned_types.strings.borrow().get(value) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::StringLiteral(
            arena.alloc(TyStringLiteral { value }),
        ));
        arena.interned_types.strings.borrow_mut().insert(value, ty);
        ty
    }

    pub fn array(arena: CheckerArena<'a>, element_type: Ty<'a>) -> Self {
        Self::intern_array(arena, element_type, false, false)
    }

    pub fn readonly_array(arena: CheckerArena<'a>, element_type: Ty<'a>) -> Self {
        Self::intern_array(arena, element_type, true, false)
    }

    pub fn generic_array(arena: CheckerArena<'a>, element_type: Ty<'a>, readonly: bool) -> Self {
        Self::intern_array(arena, element_type, readonly, true)
    }

    fn intern_array(
        arena: CheckerArena<'a>,
        element_type: Ty<'a>,
        readonly: bool,
        display_as_generic: bool,
    ) -> Self {
        let key = ArrayTypeKey {
            element_type: element_type.id(),
            readonly,
            display_as_generic,
        };
        if let Some(ty) = arena.interned_types.arrays.borrow().get(&key) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::Array(arena.alloc(TyArray {
            element_type,
            readonly,
            display_as_generic,
        })));
        arena.interned_types.arrays.borrow_mut().insert(key, ty);
        ty
    }

    pub fn tuple(arena: CheckerArena<'a>, elements: Vec<TupleElement<'a>>) -> Self {
        Self::normalized_tuple(
            arena,
            elements.into_iter().map(LabeledTupleElement::unlabeled),
            TupleReadonly::Mutable,
        )
    }

    pub fn readonly_tuple(arena: CheckerArena<'a>, elements: Vec<TupleElement<'a>>) -> Self {
        Self::normalized_tuple(
            arena,
            elements.into_iter().map(LabeledTupleElement::unlabeled),
            TupleReadonly::Readonly,
        )
    }

    pub fn tuple_with_labels(
        arena: CheckerArena<'a>,
        elements: impl IntoIterator<Item = LabeledTupleElement<'a>>,
        readonly: TupleReadonly,
    ) -> Self {
        Self::normalized_tuple(arena, elements, readonly)
    }

    fn normalized_tuple(
        arena: CheckerArena<'a>,
        elements: impl IntoIterator<Item = LabeledTupleElement<'a>>,
        readonly: TupleReadonly,
    ) -> Self {
        let elements = elements.into_iter();
        let mut normalized = Vec::with_capacity(elements.size_hint().0);
        let mut normalized_labels: Option<Vec<Option<&'a str>>> = None;
        for LabeledTupleElement { element, label } in elements {
            if let TupleElement::Rest(ty) = element
                && let TyKind::Tuple(tuple) = arena.ty_kind(ty)
            {
                if normalized.len() + tuple.elements.len() >= TUPLE_SPREAD_MAX_LENGTH {
                    return Ty::error(arena, TypeErrorKind::TupleSizeExceeded);
                }
                if let Some(tuple_labels) = tuple.labels() {
                    normalized_labels
                        .get_or_insert_with(|| vec![None; normalized.len()])
                        .extend_from_slice(tuple_labels);
                } else if let Some(labels) = &mut normalized_labels {
                    labels.resize(labels.len() + tuple.elements.len(), None);
                }
                normalized.extend(tuple.elements.iter().copied());
            } else {
                if label.is_some() {
                    normalized_labels
                        .get_or_insert_with(|| vec![None; normalized.len()])
                        .push(label);
                } else if let Some(labels) = &mut normalized_labels {
                    labels.push(None);
                }
                normalized.push(element);
            }
        }

        let readonly = readonly.is_readonly();
        let key = TupleTypeKey {
            elements: &normalized,
            labels: normalized_labels.as_deref(),
            readonly,
        };
        if let Some(ty) = arena.interned_types.tuples.borrow().get(&key) {
            return *ty;
        }
        let elements = arena.vec_from_iter(normalized);
        let labels = normalized_labels.map(|labels| arena.alloc_slice_from_iter(labels));
        let tuple = arena.alloc(TyTuple {
            elements,
            labels,
            readonly,
        });
        let ty = arena.alloc_type(TyKind::Tuple(tuple));
        arena.interned_types.tuples.borrow_mut().insert(
            TupleTypeKey {
                elements: &tuple.elements,
                labels: tuple.labels(),
                readonly,
            },
            ty,
        );
        ty
    }

    pub fn r#union(arena: CheckerArena<'a>, types: impl IntoIterator<Item = Ty<'a>>) -> Self {
        reduce_union_type(arena, types)
    }

    pub(crate) fn source_union(
        arena: CheckerArena<'a>,
        types: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        reduce_source_union_type(arena, types)
    }

    pub(crate) fn map_union(
        self,
        arena: CheckerArena<'a>,
        map: impl FnMut(Ty<'a>) -> Option<Ty<'a>>,
    ) -> Self {
        let TyKind::Union(union) = arena.ty_kind(self) else {
            return self;
        };
        Ty::union(arena, union.types.iter().copied().filter_map(map))
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
        if let Some(ty) = arena.interned_types.keyofs.borrow().get(&target.id()) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::Keyof(arena.alloc(TyKeyof { target })));
        arena
            .interned_types
            .keyofs
            .borrow_mut()
            .insert(target.id(), ty);
        ty
    }

    pub fn indexed_access(
        arena: CheckerArena<'a>,
        object_type: Ty<'a>,
        index_type: Ty<'a>,
    ) -> Self {
        let key = (object_type.id(), index_type.id());
        if let Some(ty) = arena.interned_types.indexed_accesses.borrow().get(&key) {
            return *ty;
        }
        let ty = arena.alloc_type(TyKind::IndexedAccess(arena.alloc(TyIndexedAccess {
            object_type,
            index_type,
        })));
        arena
            .interned_types
            .indexed_accesses
            .borrow_mut()
            .insert(key, ty);
        ty
    }

    pub fn conditional(
        arena: CheckerArena<'a>,
        check_type: Ty<'a>,
        extends_type: Ty<'a>,
        true_type: Ty<'a>,
        false_type: Ty<'a>,
        is_distributive: bool,
    ) -> Self {
        arena.intern_conditional(
            check_type,
            extends_type,
            true_type,
            false_type,
            is_distributive,
        )
    }

    pub fn infer(arena: CheckerArena<'a>, type_parameter: TyTypeParameter<'a>) -> Self {
        arena.alloc_type(TyKind::Infer(arena.alloc(TyInfer { type_parameter })))
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
        arena.alloc_type(TyKind::Mapped(arena.alloc(TyMapped {
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

    /// Returns `true` if the type is `unknown`.
    pub fn is_unknown(&self) -> bool {
        *self == Self::Unknown
    }

    pub fn is_error(&self, arena: CheckerArena<'a>) -> bool {
        matches!(arena.ty_kind(*self), TyKind::Error(_))
    }

    pub fn error_kind(&self, arena: CheckerArena<'a>) -> Option<TypeErrorKind> {
        match arena.ty_kind(*self) {
            TyKind::Error(kind) => Some(kind),
            _ => None,
        }
    }

    pub fn is_any_like(&self, arena: CheckerArena<'a>) -> bool {
        self.is_any() || self.is_error(arena)
    }

    /// Returns `true` if the type is `never`.
    pub fn is_never(&self) -> bool {
        *self == Self::Never
    }

    /// Returns `true` if the type is `undefined`.
    pub fn is_undefined(&self) -> bool {
        *self == Self::Undefined
    }

    /// Returns `true` if the type is a union type.
    pub fn is_union(&self, arena: CheckerArena<'a>) -> bool {
        matches!(arena.ty_kind(*self), TyKind::Union(_))
    }

    /// Returns `true` if the type is a intersection type.
    pub fn is_intersection(&self, arena: CheckerArena<'a>) -> bool {
        matches!(arena.ty_kind(*self), TyKind::Intersection(_))
    }

    pub(crate) fn is_transparent_type_alias_union_constituent(
        &self,
        arena: CheckerArena<'a>,
    ) -> bool {
        matches!(
            arena.ty_kind(*self),
            TyKind::String
                | TyKind::Number
                | TyKind::Boolean
                | TyKind::Bigint
                | TyKind::Symbol
                | TyKind::Undefined
                | TyKind::Null
                | TyKind::Void
                | TyKind::Never
                | TyKind::Any
                | TyKind::Error(_)
                | TyKind::Unknown
                | TyKind::PrimitiveObject
                | TyKind::StringLiteral(_)
                | TyKind::NumberLiteral(_)
                | TyKind::BooleanLiteral(_)
                | TyKind::BigIntLiteral(_)
                | TyKind::TemplateLiteral(_)
                | TyKind::UniqueSymbol(_)
        )
    }
    /// Returns `true` if the type is string-like and can be used for concatenating two strings at runtime
    pub fn is_string_like(&self, arena: CheckerArena<'a>) -> bool {
        matches!(
            arena.ty_kind(*self),
            TyKind::String | TyKind::StringLiteral(_) | TyKind::TemplateLiteral(_)
        )
    }

    /// Returns `true` if the type is a numerical index type.
    pub fn is_number_like(&self, arena: CheckerArena<'a>) -> bool {
        matches!(
            arena.ty_kind(*self),
            TyKind::Number | TyKind::NumberLiteral(_)
        )
    }

    /// Returns `true` if the type is a BigInt type.
    pub fn is_bigint_like(&self, arena: CheckerArena<'a>) -> bool {
        matches!(
            arena.ty_kind(*self),
            TyKind::Bigint | TyKind::BigIntLiteral(_)
        )
    }

    /// Returns `true` if the type is directly represented by a `TyFunction`.
    pub fn is_function(&self, arena: CheckerArena<'a>) -> bool {
        matches!(arena.ty_kind(*self), TyKind::Function(_))
    }

    pub fn enum_variant_name(self, arena: CheckerArena<'a>) -> &'static str {
        match arena.ty_kind(self) {
            TyKind::None => "TyNone",
            TyKind::Number => "TyNumber",
            TyKind::String => "TyString",
            TyKind::Boolean => "TyBoolean",
            TyKind::Bigint => "TyBigint",
            TyKind::Symbol => "TySymbol",
            TyKind::UniqueSymbol(_) => "TyUniqueSymbol",
            TyKind::Undefined => "TyUndefined",
            TyKind::Null => "TyNull",
            TyKind::Any => "TyAny",
            TyKind::Error(_) => "TyError",
            TyKind::Unknown => "TyUnknown",
            TyKind::Void => "TyVoid",
            TyKind::Never => "TyNever",
            TyKind::Object(_) => "TyObject",
            TyKind::ModuleNamespace(_) => "TyModuleNamespace",
            TyKind::PrimitiveObject => "TyPrimitiveObject",
            TyKind::This => "TyThis",
            TyKind::GlobalThis => "TyGlobalThis",
            TyKind::Function(_) => "TyFunction",
            TyKind::TypeReference(_) => "TyTypeReference",
            TyKind::TypeQuery(_) => "TyTypeQuery",
            TyKind::StringLiteral(_) => "TyStringLiteral",
            TyKind::NumberLiteral(_) => "TyNumberLiteral",
            TyKind::BooleanLiteral(_) => "TyBooleanLiteral",
            TyKind::BigIntLiteral(_) => "TyBigIntLiteral",
            TyKind::TemplateLiteral(_) => "TyTemplateLiteral",
            TyKind::Array(_) => "TyArray",
            TyKind::Tuple(_) => "TyTuple",
            TyKind::Union(_) => "TyUnion",
            TyKind::Intersection(_) => "TyIntersection",
            TyKind::Keyof(_) => "TyKeyof",
            TyKind::IndexedAccess(_) => "TyIndexedAccess",
            TyKind::Conditional(_) => "TyConditional",
            TyKind::Infer(_) => "TyInfer",
            TyKind::Mapped(_) => "TyMapped",
        }
    }

    #[allow(dead_code)]
    pub fn to_type_string(self, arena: CheckerArena<'a>) -> String {
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
        self.to_type_string_with_flags(
            arena,
            replace_type_reference,
            TypeFormatFlags::PRESERVE_PROPERTY_NAME_QUOTES,
            depth,
        )
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

        let flags = if current == 0 {
            flags
        } else {
            flags & !TypeFormatFlags::PRESERVE_PROPERTY_NAME_QUOTES
        };
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
        match arena.ty_kind(self) {
            TyKind::None => "none".to_string(),
            TyKind::Number => "number".to_string(),
            TyKind::String => "string".to_string(),
            TyKind::Boolean => "boolean".to_string(),
            TyKind::Bigint => "bigint".to_string(),
            TyKind::Symbol => "symbol".to_string(),
            TyKind::UniqueSymbol(_) => "unique symbol".to_string(),
            TyKind::Undefined => "undefined".to_string(),
            TyKind::Null => "null".to_string(),
            TyKind::Any => "any".to_string(),
            TyKind::Error(_) => "any".to_string(),
            TyKind::Unknown => "unknown".to_string(),
            TyKind::Void => "void".to_string(),
            TyKind::Never => "never".to_string(),
            TyKind::PrimitiveObject => "object".to_string(),
            TyKind::This => "this".to_string(),
            TyKind::Object(object) => {
                if object.is_constructor_type
                    && let Some(signature) = object.signatures().first()
                {
                    return constructor_type_to_string(arena, *signature, &|_| None, flags, depth);
                }
                if object.properties.is_empty()
                    && object.signatures().is_empty()
                    && object.index_infos().is_empty()
                {
                    return "{}".to_string();
                }

                let signatures = object
                    .signatures()
                    .iter()
                    .filter(|signature| signature.kind == SignatureKind::Call)
                    .chain(
                        object
                            .signatures()
                            .iter()
                            .filter(|signature| signature.kind == SignatureKind::Construct),
                    );
                let members = signatures
                    .map(|signature| {
                        signature.to_type_string_with_flags(arena, &|_| None, flags, depth)
                    })
                    .chain(object.index_infos().iter().map(|info| {
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
                            && let TyKind::Function(function) = arena.ty_kind(property.ty)
                        {
                            format!(
                                "{}{}{};",
                                readonly,
                                property_name_to_type_string(property, flags),
                                signature_to_type_string(arena, function, &|_| None, flags, depth,)
                            )
                        } else {
                            format!(
                                "{}{}: {};",
                                readonly,
                                property_name_to_type_string(property, flags),
                                property.ty.to_type_string_with_flags(
                                    arena,
                                    replace_type_reference,
                                    flags
                                        | TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE
                                        | if property
                                            .flags
                                            .contains(TyPropertyFlags::TYPE_SINGLE_QUOTED)
                                        {
                                            TypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL
                                        } else {
                                            TypeFormatFlags::NONE
                                        },
                                    depth,
                                )
                            )
                        }
                    }))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("{{ {members} }}")
            }
            TyKind::ModuleNamespace(namespace) => format!("typeof {}", namespace.name),
            TyKind::Function(function) => {
                function_type_to_string(arena, function, &|_| None, flags, depth)
            }
            TyKind::TypeReference(reference) => {
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
            TyKind::TypeQuery(query) => {
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
            TyKind::GlobalThis => "typeof globalThis".to_string(),
            TyKind::StringLiteral(string_literal) => quoted_property_name(
                string_literal.value,
                flags.contains(TypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL),
            ),
            TyKind::NumberLiteral(number_literal) => {
                // Print the base-10 representation of the number
                if number_literal.value.is_zero() {
                    // Treat +0 and -0 as the same when printing.
                    "0".to_string()
                } else {
                    number_literal.value.to_string()
                }
            }
            TyKind::BooleanLiteral(value) => value.to_string(),
            TyKind::BigIntLiteral(big_int_literal) => format!("{}n", big_int_literal.value),
            TyKind::TemplateLiteral(template_literal) => {
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
            TyKind::Array(array) => {
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
            TyKind::Tuple(tuple) => {
                let elements = tuple
                    .elements
                    .iter()
                    .enumerate()
                    .map(|(index, element)| {
                        let label = tuple.labels().and_then(|labels| labels[index]);
                        match (label, element) {
                            (Some(label), TupleElement::Regular(ty)) => format!(
                                "{label}: {}",
                                ty.to_type_string_with_flags(
                                    arena,
                                    replace_type_reference,
                                    flags,
                                    depth,
                                )
                            ),
                            (Some(label), TupleElement::Rest(ty)) => format!(
                                "...{label}: {}",
                                ty.to_type_string_with_flags(
                                    arena,
                                    replace_type_reference,
                                    flags,
                                    depth,
                                )
                            ),
                            (Some(label), TupleElement::Optional(ty)) => format!(
                                "{label}?: {}",
                                ty.to_type_string_with_flags(
                                    arena,
                                    replace_type_reference,
                                    flags,
                                    depth,
                                )
                            ),
                            (None, TupleElement::Regular(ty)) => ty.to_type_string_with_flags(
                                arena,
                                replace_type_reference,
                                flags,
                                depth,
                            ),
                            (None, TupleElement::Rest(ty)) => format!(
                                "...{}",
                                ty.to_type_string_with_flags(
                                    arena,
                                    replace_type_reference,
                                    flags,
                                    depth,
                                )
                            ),
                            (None, TupleElement::Optional(ty)) => {
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
            TyKind::Union(union) => union
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
            TyKind::Intersection(intersection) => intersection
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
            TyKind::Keyof(keyof) => {
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
            TyKind::IndexedAccess(indexed_access) => {
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
            TyKind::Conditional(conditional) => {
                let check_type = conditional.check_type.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags,
                    depth,
                );
                let extends_type = conditional.extends_type.to_type_string_with_flags(
                    arena,
                    replace_type_reference,
                    flags
                        | if conditional.extends_type.is_function(arena) {
                            TypeFormatFlags::PARENTHESIZE_CONDITIONAL_RETURN
                        } else {
                            TypeFormatFlags::NONE
                        },
                    depth,
                );
                let check_type = if conditional.check_type.display_needs_parentheses(arena) {
                    format!("({check_type})")
                } else {
                    check_type
                };
                let extends_type = if matches!(
                    arena.ty_kind(conditional.extends_type),
                    TyKind::Conditional(_)
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
            TyKind::Infer(infer) => format!(
                "infer {}",
                type_parameter_to_type_string(
                    arena,
                    &infer.type_parameter,
                    &|_| None,
                    flags,
                    depth,
                )
            ),
            TyKind::Mapped(mapped) => {
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
            arena.ty_kind(*self),
            TyKind::Function(_)
                | TyKind::Union(_)
                | TyKind::Intersection(_)
                | TyKind::Conditional(_)
                | TyKind::Infer(_)
        ) || matches!(arena.ty_kind(*self), TyKind::Object(object) if object.is_constructor_type)
    }

    pub(crate) fn with_signatures(
        self,
        arena: CheckerArena<'a>,
        signatures: impl IntoIterator<Item = Signature<'a>>,
    ) -> Self {
        let TyKind::Object(object) = arena.ty_kind(self) else {
            return self;
        };
        Self::object_from_slices(
            arena,
            object.properties,
            arena.alloc_slice_from_iter(signatures),
            object.index_infos(),
            object.is_constructor_type,
        )
    }

    pub(crate) fn with_index_infos(
        self,
        arena: CheckerArena<'a>,
        index_infos: impl IntoIterator<Item = IndexInfo<'a>>,
    ) -> Self {
        let TyKind::Object(object) = arena.ty_kind(self) else {
            return self;
        };
        Self::object_from_slices(
            arena,
            object.properties,
            object.signatures(),
            arena.alloc_slice_from_iter(index_infos),
            object.is_constructor_type,
        )
    }

    pub(crate) fn with_constructor_type(self, arena: CheckerArena<'a>) -> Self {
        let TyKind::Object(object) = arena.ty_kind(self) else {
            return self;
        };
        if object.is_constructor_type {
            return self;
        }
        Self::object_from_slices(
            arena,
            object.properties,
            object.signatures(),
            object.index_infos(),
            true,
        )
    }

    /// Returns `true` if the type is an object with no properties or signatures and has index infos.
    pub fn is_index_signature_object(&self, arena: CheckerArena<'a>) -> bool {
        let TyKind::Object(object) = arena.ty_kind(*self) else {
            return false;
        };
        object.signatures().is_empty()
            && object.properties.is_empty()
            && !object.index_infos().is_empty()
    }

    /// Returns the index infos of the type, or `None` if the type is not an object with index infos.
    pub fn index_infos(&self, arena: CheckerArena<'a>) -> Option<&'a [IndexInfo<'a>]> {
        let TyKind::Object(object) = arena.ty_kind(*self) else {
            return None;
        };
        if object.index_infos().is_empty() {
            None
        } else {
            Some(object.index_infos())
        }
    }

    /// Returns the element type of an array type, or `None` if the type is not an array.
    pub fn array_element_type(&self, arena: CheckerArena<'a>) -> Option<Self> {
        let TyKind::Array(array) = arena.ty_kind(*self) else {
            return None;
        };
        Some(array.element_type)
    }

    /// Returns the string value of the type (if applicable).
    pub fn string_value(&self, arena: CheckerArena<'a>) -> Option<&'a str> {
        match arena.ty_kind(*self) {
            TyKind::StringLiteral(string_literal) => Some(string_literal.value),
            // TODO(completeness): Handle template literals
            _ => None,
        }
    }

    /// Returns the type, unioned with `undefined`.
    #[must_use]
    pub fn or_undefined(&self, arena: CheckerArena<'a>) -> Self {
        if *self == Ty::Undefined {
            *self
        } else {
            Self::union(arena, [*self, Ty::Undefined])
        }
    }

    pub(crate) fn should_display_implicit_default_type_argument(
        &self,
        arena: CheckerArena<'a>,
    ) -> bool {
        !matches!(
            arena.ty_kind(*self),
            TyKind::Any | TyKind::Error(_) | TyKind::Unknown
        )
    }
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
    pub kind: SignatureKind,
    pub ty: Ty<'a>,
    pub is_abstract: bool,
}

impl<'a> Signature<'a> {
    pub(crate) fn new(kind: SignatureKind, ty: Ty<'a>) -> Self {
        Self {
            kind,
            ty,
            is_abstract: false,
        }
    }

    pub(crate) fn abstract_construct(ty: Ty<'a>) -> Self {
        Self {
            kind: SignatureKind::Construct,
            ty,
            is_abstract: true,
        }
    }

    pub fn function(self, arena: CheckerArena<'a>) -> &'a TyFunction<'a> {
        let TyKind::Function(function) = arena.ty_kind(self.ty) else {
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
    pub name: &'a str,
    /// The type of the index key. The `K` in `{ [k: K]: V }` or `string` in `{ [k: string]: number }`
    pub key_type: Ty<'a>,
    /// The type of the index value. The `V` in `{ [k: K]: V }` or `string` in `{ [k: string]: number }`
    pub value_type: Ty<'a>,
    /// Whether the index returns a readonly value.
    pub readonly: bool,
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

fn constructor_type_to_string<'a>(
    arena: CheckerArena<'a>,
    signature: Signature<'a>,
    replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
    flags: TypeFormatFlags,
    depth: &Cell<usize>,
) -> String {
    let function = signature.function(arena);
    let (type_parameters, parameters) =
        function_type_head_to_string(arena, function, replace_type_reference, flags, depth);
    let prefix = if signature.is_abstract {
        "abstract new"
    } else {
        "new"
    };
    format!(
        "{prefix} {type_parameters}({parameters}) => {}",
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
    let return_type = function.type_predicate.map_or_else(
        || {
            function.return_type.to_type_string_with_flags(
                arena,
                replace_type_reference,
                flags | TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE,
                depth,
            )
        },
        |predicate| {
            type_predicate_to_type_string(arena, predicate, replace_type_reference, flags, depth)
        },
    );
    if flags.contains(TypeFormatFlags::PARENTHESIZE_CONDITIONAL_RETURN)
        && function.type_predicate.is_none()
        && matches!(arena.ty_kind(function.return_type), TyKind::Conditional(_))
    {
        format!("({return_type})")
    } else {
        return_type
    }
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
                if function.display_type_parameters_as_arguments {
                    type_parameter.name.to_string()
                } else {
                    type_parameter_to_type_string(
                        arena,
                        type_parameter,
                        replace_type_reference,
                        flags,
                        depth,
                    )
                }
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
                flags | TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE,
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
        && let TyKind::Tuple(tuple) = arena.ty_kind(parameter.ty)
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

pub(crate) fn property_name_flags(key: &PropertyKey<'_>) -> TyPropertyFlags {
    match key {
        PropertyKey::StringLiteral(literal) => literal
            .raw
            .as_ref()
            .and_then(|raw| raw.as_str().chars().next())
            .map_or(TyPropertyFlags::NONE, |delimiter| {
                if delimiter == '\'' {
                    TyPropertyFlags::SINGLE_QUOTED
                } else {
                    TyPropertyFlags::NONE
                }
            }),
        _ => TyPropertyFlags::NONE,
    }
}

fn property_name_to_type_string(
    property: &TyProperty<'_>,
    format_flags: TypeFormatFlags,
) -> String {
    let name = if property.computed {
        format!("[{}]", property.name)
    } else if is_identifier_name(property.name) || is_numeric_property_name(property.name) {
        property.name.to_string()
    } else {
        quoted_property_name(
            property.name,
            format_flags.contains(TypeFormatFlags::PRESERVE_PROPERTY_NAME_QUOTES)
                && property.flags.contains(TyPropertyFlags::SINGLE_QUOTED),
        )
    };
    if property.optional {
        format!("{name}?")
    } else {
        name
    }
}

fn quoted_property_name(name: &str, single_quoted: bool) -> String {
    let mut quoted = String::with_capacity(name.len() + 2);
    let delimiter = if single_quoted { '\'' } else { '"' };
    quoted.push(delimiter);
    for character in name.chars() {
        match character {
            '\\' => quoted.push_str("\\\\"),
            '\n' => quoted.push_str("\\n"),
            '\r' => quoted.push_str("\\r"),
            '\t' => quoted.push_str("\\t"),
            _ if character == delimiter => {
                quoted.push('\\');
                quoted.push(character);
            }
            _ => quoted.push(character),
        }
    }
    quoted.push(delimiter);
    quoted
}

fn is_numeric_property_name(name: &str) -> bool {
    name.parse::<f64>().is_ok()
        || name
            .strip_prefix("0x")
            .or_else(|| name.strip_prefix("0X"))
            .is_some_and(|digits| {
                !digits.is_empty() && digits.chars().all(|char| char.is_ascii_hexdigit())
            })
        || name
            .strip_prefix("0b")
            .or_else(|| name.strip_prefix("0B"))
            .is_some_and(|digits| {
                !digits.is_empty() && digits.chars().all(|char| matches!(char, '0' | '1'))
            })
        || name
            .strip_prefix("0o")
            .or_else(|| name.strip_prefix("0O"))
            .is_some_and(|digits| {
                !digits.is_empty() && digits.chars().all(|char| matches!(char, '0'..='7'))
            })
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
#[path = "types_test.rs"]
mod types_test;
