use crate::types::{CheckerArena, Ty, TyKind, TyTemplateLiteral, TypeId};
use rustc_hash::FxHashSet;
use smallvec::SmallVec;

const UNION_INLINE_TYPE_CAPACITY: usize = 8;
const UNION_INLINE_SEEN_ID_CAPACITY: usize = 16;

type UnionTypes<'a> = SmallVec<[Ty<'a>; UNION_INLINE_TYPE_CAPACITY]>;

enum SeenTypeIds {
    Inline(SmallVec<[TypeId; UNION_INLINE_SEEN_ID_CAPACITY]>),
    Spilled(FxHashSet<TypeId>),
}

impl SeenTypeIds {
    fn new() -> Self {
        Self::Inline(SmallVec::new())
    }

    fn insert(&mut self, id: TypeId) -> bool {
        match self {
            Self::Inline(ids) => {
                if ids.contains(&id) {
                    return false;
                }
                if ids.len() < UNION_INLINE_SEEN_ID_CAPACITY {
                    ids.push(id);
                    return true;
                }

                let mut spilled = FxHashSet::default();
                spilled.reserve(ids.len() * 2);
                spilled.extend(ids.iter().copied());
                let inserted = spilled.insert(id);
                *self = Self::Spilled(spilled);
                inserted
            }
            Self::Spilled(ids) => ids.insert(id),
        }
    }
}

pub(crate) struct UnionAccumulator<'a> {
    arena: CheckerArena<'a>,
    types: UnionTypes<'a>,
    seen_ids: SeenTypeIds,
}

impl<'a> UnionAccumulator<'a> {
    pub(crate) fn new(arena: CheckerArena<'a>) -> Self {
        Self {
            arena,
            types: SmallVec::new(),
            seen_ids: SeenTypeIds::new(),
        }
    }

    pub(crate) fn add(&mut self, ty: Ty<'a>) {
        add_type_to_union(self.arena, &mut self.types, &mut self.seen_ids, ty);
    }

    pub(crate) fn extend(&mut self, types: impl IntoIterator<Item = Ty<'a>>) {
        for ty in types {
            self.add(ty);
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.types.is_empty()
    }

    pub(crate) fn try_build(self) -> Option<Ty<'a>> {
        (!self.is_empty()).then(|| self.build())
    }

    pub(crate) fn build(self) -> Ty<'a> {
        self.build_with_nullish_normalization(true)
    }

    fn build_with_nullish_normalization(mut self, normalize_nullish_order: bool) -> Ty<'a> {
        if let Some(error) = self.types.iter().find(|ty| ty.is_error(self.arena)) {
            return *error;
        }
        if self.types.contains(&Ty::Any) {
            return Ty::Any;
        }
        if self.types.contains(&Ty::Unknown) {
            return Ty::Unknown;
        }

        remove_redundant_literal_types(self.arena, &mut self.types);
        reduce_boolean_literal_union(self.arena, &mut self.types);

        if self.types.len() > 1 {
            self.types.retain(|ty| !ty.is_never());
        }

        if normalize_nullish_order {
            normalize_null_undefined_order(&mut self.types);
        }

        if self.types.len() == 1 {
            return self.types[0];
        }

        self.arena.intern_union(self.types)
    }
}

pub fn reduce_union_type<'a>(
    arena: CheckerArena<'a>,
    types: impl IntoIterator<Item = Ty<'a>>,
) -> Ty<'a> {
    let mut accumulator = UnionAccumulator::new(arena);
    accumulator.extend(types);
    accumulator.build()
}

pub(crate) fn reduce_source_union_type<'a>(
    arena: CheckerArena<'a>,
    types: impl IntoIterator<Item = Ty<'a>>,
) -> Ty<'a> {
    let mut accumulator = UnionAccumulator::new(arena);
    accumulator.extend(types);
    let contains_type_parameter = accumulator.types.iter().any(|ty| {
        matches!(
            arena.ty_kind(*ty),
            TyKind::TypeReference(reference) if reference.is_bare() && reference.target.is_none()
        )
    });
    accumulator.build_with_nullish_normalization(contains_type_parameter)
}

fn add_type_to_union<'a>(
    arena: CheckerArena<'a>,
    type_set: &mut UnionTypes<'a>,
    seen_ids: &mut SeenTypeIds,
    ty: Ty<'a>,
) {
    if !seen_ids.insert(ty.id()) {
        return;
    }
    if let TyKind::Union(union) = arena.ty_kind(ty) {
        for ty in &union.types {
            add_type_to_union(arena, type_set, seen_ids, *ty);
        }
    } else if let TyKind::TypeReference(reference) = arena.ty_kind(ty)
        && reference.is_bare()
        && reference.target.is_some()
    {
        // Symbol-backed references are interned, so handle identity is sufficient here.
        type_set.push(ty);
    } else if matches!(
        arena.ty_kind(ty),
        TyKind::StringLiteral(_)
            | TyKind::NumberLiteral(_)
            | TyKind::BigIntLiteral(_)
            | TyKind::TemplateLiteral(_)
    ) {
        // Canonical literal types are interned, so `seen_ids` has already removed duplicates.
        type_set.push(ty);
    } else if (matches!(arena.ty_kind(ty), TyKind::Object(_)) && !arena.is_fresh_object_literal(ty))
        || !type_set
            .iter()
            .any(|existing| union_constituents_are_identical(arena, *existing, ty))
    {
        type_set.push(ty);
    }
}

fn union_constituents_are_identical<'a>(
    arena: CheckerArena<'a>,
    left: Ty<'a>,
    right: Ty<'a>,
) -> bool {
    if left == right {
        return true;
    }
    match (arena.ty_kind(left), arena.ty_kind(right)) {
        (TyKind::Object(_), TyKind::Object(_)) => {
            arena.is_fresh_object_literal(left)
                && arena.is_fresh_object_literal(right)
                && arena.is_type_identical_to(left, right)
        }
        (TyKind::Object(_), _) | (_, TyKind::Object(_)) => false,
        _ => arena.is_type_identical_to(left, right),
    }
}

pub(crate) fn reduce_intersection_type<'a>(
    arena: CheckerArena<'a>,
    types: impl IntoIterator<Item = Ty<'a>>,
) -> Ty<'a> {
    let mut type_set = Vec::new();
    let mut seen_ids = FxHashSet::default();
    for ty in types {
        add_type_to_intersection(arena, &mut type_set, &mut seen_ids, ty);
    }

    if let Some(error) = type_set.iter().find(|ty| ty.is_error(arena)) {
        return *error;
    }
    if type_set.contains(&Ty::Any) {
        return Ty::Any;
    }

    let empty_object = type_set
        .iter()
        .find(|ty| matches!(arena.ty_kind(**ty), TyKind::Object(object) if object.is_empty()));
    if let Some(empty_object) = empty_object.copied() {
        for ty in &mut type_set {
            if matches!(arena.ty_kind(*ty), TyKind::Union(_)) {
                *ty = intersect_with_empty_object(arena, *ty, empty_object);
            }
        }
        if type_set
            .iter()
            .any(|ty| matches!(arena.ty_kind(*ty), TyKind::Null | TyKind::Undefined))
        {
            return Ty::Never;
        }
    }
    if type_set.contains(&Ty::Never) {
        return Ty::Never;
    }

    if type_set.len() > 1 {
        type_set.retain(|ty| *ty != Ty::Unknown);
    }

    remove_redundant_primitive_intersection_types(arena, &mut type_set);

    let has_object_like_member = type_set
        .iter()
        .filter(|ty| !matches!(arena.ty_kind(**ty), TyKind::Object(object) if object.is_empty()))
        .any(|ty| is_empty_object_intersection_identity_target(arena, *ty));
    if has_object_like_member {
        type_set.retain(
            |ty| !matches!(arena.ty_kind(*ty), TyKind::Object(object) if object.is_empty()),
        );
    }

    match type_set.as_slice() {
        [] => arena.object([]),
        [ty] => *ty,
        _ => arena.intern_intersection(type_set),
    }
}

fn add_type_to_intersection<'a>(
    arena: CheckerArena<'a>,
    type_set: &mut Vec<Ty<'a>>,
    seen_ids: &mut FxHashSet<TypeId>,
    ty: Ty<'a>,
) {
    if !seen_ids.insert(ty.id()) {
        return;
    }
    if let TyKind::Intersection(intersection) = arena.ty_kind(ty) {
        for ty in &intersection.types {
            add_type_to_intersection(arena, type_set, seen_ids, *ty);
        }
    } else {
        type_set.push(ty);
    }
}

fn intersect_with_empty_object<'a>(
    arena: CheckerArena<'a>,
    ty: Ty<'a>,
    empty_object: Ty<'a>,
) -> Ty<'a> {
    match arena.ty_kind(ty) {
        TyKind::Union(union) => arena.union(
            union
                .types
                .iter()
                .map(|ty| intersect_with_empty_object(arena, *ty, empty_object)),
        ),
        TyKind::Null | TyKind::Undefined => Ty::Never,
        TyKind::Unknown => empty_object,
        TyKind::Object(object) if object.is_empty() => ty,
        _ => arena.intersection([ty, empty_object]),
    }
}

fn is_empty_object_intersection_identity_target<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> bool {
    match arena.ty_kind(ty) {
        TyKind::Number
        | TyKind::String
        | TyKind::Boolean
        | TyKind::Bigint
        | TyKind::Symbol
        | TyKind::PrimitiveObject
        | TyKind::NumberLiteral(_)
        | TyKind::StringLiteral(_)
        | TyKind::BooleanLiteral(_)
        | TyKind::BigIntLiteral(_)
        | TyKind::UniqueSymbol(_)
        | TyKind::TemplateLiteral(_)
        | TyKind::ModuleNamespace(_)
        | TyKind::Function(_)
        | TyKind::Class(_)
        | TyKind::TypeQuery(_)
        | TyKind::Array(_)
        | TyKind::Tuple(_)
        | TyKind::Mapped(_)
        | TyKind::GlobalThis => true,
        TyKind::Object(_) => true,
        TyKind::Union(union) => union
            .types
            .iter()
            .all(|ty| is_empty_object_intersection_identity_target(arena, *ty)),
        _ => false,
    }
}

fn remove_redundant_primitive_intersection_types<'a>(
    arena: CheckerArena<'a>,
    type_set: &mut Vec<Ty<'a>>,
) {
    let has_string_literal = type_set.iter().any(|ty| {
        matches!(
            arena.ty_kind(*ty),
            TyKind::StringLiteral(_) | TyKind::TemplateLiteral(_)
        )
    });
    let has_number_literal = type_set
        .iter()
        .any(|ty| matches!(arena.ty_kind(*ty), TyKind::NumberLiteral(_)));
    let has_boolean_literal = type_set
        .iter()
        .any(|ty| matches!(arena.ty_kind(*ty), TyKind::BooleanLiteral(_)));
    let has_bigint_literal = type_set
        .iter()
        .any(|ty| matches!(arena.ty_kind(*ty), TyKind::BigIntLiteral(_)));

    type_set.retain(|ty| match arena.ty_kind(*ty) {
        TyKind::String => !has_string_literal,
        TyKind::Number => !has_number_literal,
        TyKind::Boolean => !has_boolean_literal,
        TyKind::Bigint => !has_bigint_literal,
        _ => true,
    });
}

fn normalize_null_undefined_order(type_set: &mut [Ty<'_>]) {
    let Some(null_index) = type_set.iter().position(|ty| *ty == Ty::Null) else {
        return;
    };
    let Some(undefined_index) = type_set.iter().position(|ty| *ty == Ty::Undefined) else {
        return;
    };
    if undefined_index < null_index {
        type_set.swap(undefined_index, null_index);
    }
}

fn remove_redundant_literal_types<'a>(arena: CheckerArena<'a>, type_set: &mut UnionTypes<'a>) {
    let has_string = type_set.contains(&Ty::String);
    let has_number = type_set.contains(&Ty::Number);
    let has_boolean = type_set.contains(&Ty::Boolean);
    let has_bigint = type_set.contains(&Ty::Bigint);
    let template_literals = (!has_string).then(|| {
        type_set
            .iter()
            .filter_map(|ty| match arena.ty_kind(*ty) {
                TyKind::TemplateLiteral(template_literal) => Some((*ty, template_literal)),
                _ => None,
            })
            .collect::<Vec<_>>()
    });

    type_set.retain(|ty| match arena.ty_kind(*ty) {
        TyKind::StringLiteral(string_literal) => {
            template_literals.as_ref().is_some_and(|templates| {
                !templates.iter().any(|(_, template_literal)| {
                    template_literal_matches_string(arena, template_literal, string_literal.value)
                })
            })
        }
        TyKind::TemplateLiteral(template_literal) => {
            template_literals.as_ref().is_some_and(|templates| {
                template_literal_static_value(template_literal).is_none_or(|value| {
                    !templates.iter().any(|(candidate_ty, candidate)| {
                        !arena.is_type_identical_to(*candidate_ty, *ty)
                            && template_literal_matches_string(arena, candidate, value)
                    })
                })
            })
        }
        TyKind::NumberLiteral(_) => !has_number,
        TyKind::BooleanLiteral(_) => !has_boolean,
        TyKind::BigIntLiteral(_) => !has_bigint,
        _ => true,
    });
}

fn reduce_boolean_literal_union<'a>(arena: CheckerArena<'a>, type_set: &mut UnionTypes<'a>) {
    let has_true = type_set
        .iter()
        .any(|ty| matches!(arena.ty_kind(*ty), TyKind::BooleanLiteral(true)));
    let has_false = type_set
        .iter()
        .any(|ty| matches!(arena.ty_kind(*ty), TyKind::BooleanLiteral(false)));
    if has_true && has_false {
        type_set.retain(|ty| !matches!(arena.ty_kind(*ty), TyKind::BooleanLiteral(_)));
        if !type_set.contains(&Ty::Boolean) {
            type_set.push(Ty::Boolean);
        }
    }
}

fn template_literal_matches_string<'a>(
    arena: CheckerArena<'a>,
    template_literal: &TyTemplateLiteral<'a>,
    value: &str,
) -> bool {
    if let Some(static_value) = template_literal_static_value(template_literal) {
        return static_value == value;
    }

    let Some(first_quasi) = template_literal.quasis.first() else {
        return false;
    };
    if !value.starts_with(first_quasi.value) {
        return false;
    }
    let mut seen = FxHashSet::default();
    template_literal_remaining_matches(
        arena,
        template_literal,
        0,
        value,
        first_quasi.value.len(),
        &mut seen,
    )
}

fn template_literal_remaining_matches<'a>(
    arena: CheckerArena<'a>,
    template_literal: &TyTemplateLiteral<'a>,
    expression_index: usize,
    value: &str,
    offset: usize,
    seen: &mut FxHashSet<(usize, usize)>,
) -> bool {
    if !seen.insert((expression_index, offset)) {
        return false;
    }

    let Some(expression) = template_literal.expressions.get(expression_index) else {
        return offset == value.len();
    };
    let next_quasi = template_literal
        .quasis
        .get(expression_index + 1)
        .map_or("", |quasi| quasi.value);

    match arena.ty_kind(*expression) {
        TyKind::String => {
            if next_quasi.is_empty() {
                return string_split_indices(&value[offset..]).any(|split_index| {
                    template_literal_remaining_matches(
                        arena,
                        template_literal,
                        expression_index + 1,
                        value,
                        offset + split_index,
                        seen,
                    )
                });
            }

            let mut search_start = offset;
            while let Some(found_index) = value[search_start..].find(next_quasi) {
                let match_index = search_start + found_index;
                let next_index = match_index + next_quasi.len();
                if template_literal_remaining_matches(
                    arena,
                    template_literal,
                    expression_index + 1,
                    value,
                    next_index,
                    seen,
                ) {
                    return true;
                }
                search_start = next_char_boundary(value, match_index + 1);
            }
            false
        }
        TyKind::StringLiteral(string_literal) => {
            let Some(remaining) = value[offset..].strip_prefix(string_literal.value) else {
                return false;
            };
            let Some(remaining) = remaining.strip_prefix(next_quasi) else {
                return false;
            };
            template_literal_remaining_matches(
                arena,
                template_literal,
                expression_index + 1,
                value,
                value.len() - remaining.len(),
                seen,
            )
        }
        _ => false,
    }
}

fn next_char_boundary(value: &str, byte_index: usize) -> usize {
    let mut index = byte_index.min(value.len());
    while index < value.len() && !value.is_char_boundary(index) {
        index += 1;
    }
    index
}

fn template_literal_static_value<'a>(template_literal: &TyTemplateLiteral<'a>) -> Option<&'a str> {
    if !template_literal.expressions.is_empty() || template_literal.quasis.len() != 1 {
        return None;
    }
    Some(template_literal.quasis[0].value)
}

fn string_split_indices(value: &str) -> impl Iterator<Item = usize> + '_ {
    value
        .char_indices()
        .map(|(index, _)| index)
        .chain(std::iter::once(value.len()))
}
