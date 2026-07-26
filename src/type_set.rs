use std::collections::HashSet;

use crate::types::{CheckerArena, Ty, TyTemplateLiteral, TypeData, TypeId};

pub fn reduce_union_type<'a>(
    arena: CheckerArena<'a>,
    types: impl IntoIterator<Item = Ty<'a>>,
) -> Ty<'a> {
    let mut type_set = Vec::new();
    let mut seen_ids = HashSet::new();
    for ty in types {
        add_type_to_union(arena, &mut type_set, &mut seen_ids, ty);
    }

    if type_set.contains(&Ty::Any) {
        return Ty::any();
    }
    if type_set.contains(&Ty::Unknown) {
        return Ty::unknown();
    }

    remove_redundant_literal_types(arena, &mut type_set);
    reduce_boolean_literal_union(arena, &mut type_set);

    if type_set.len() > 1 {
        type_set.retain(|ty| !ty.is_never());
    }

    // TODO(perf): this is just for nicer display purposes but we
    // should handle this when printing instead, with flags?
    normalize_null_undefined_order(&mut type_set);

    if type_set.len() == 1 {
        return type_set[0];
    }

    arena.intern_union(type_set)
}

fn add_type_to_union<'a>(
    arena: CheckerArena<'a>,
    type_set: &mut Vec<Ty<'a>>,
    seen_ids: &mut HashSet<TypeId>,
    ty: Ty<'a>,
) {
    if !seen_ids.insert(ty.id()) {
        return;
    }
    if let TypeData::Union(union) = arena.type_data(ty) {
        for ty in &union.types {
            add_type_to_union(arena, type_set, seen_ids, *ty);
        }
    } else if let TypeData::TypeReference(reference) = arena.type_data(ty)
        && reference.is_bare()
        && reference.target.is_some()
    {
        // Symbol-backed references are interned, so handle identity is sufficient here.
        type_set.push(ty);
    } else if (matches!(arena.type_data(ty), TypeData::Object(_))
        && !arena.is_fresh_object_literal(ty))
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
    match (arena.type_data(left), arena.type_data(right)) {
        (TypeData::Object(_), TypeData::Object(_)) => {
            arena.is_fresh_object_literal(left)
                && arena.is_fresh_object_literal(right)
                && arena.is_type_identical_to(left, right)
        }
        (TypeData::Object(_), _) | (_, TypeData::Object(_)) => false,
        _ => arena.is_type_identical_to(left, right),
    }
}

pub(crate) fn reduce_intersection_type<'a>(
    arena: CheckerArena<'a>,
    types: impl IntoIterator<Item = Ty<'a>>,
) -> Ty<'a> {
    let mut type_set = Vec::new();
    let mut seen_ids = HashSet::new();
    for ty in types {
        add_type_to_intersection(arena, &mut type_set, &mut seen_ids, ty);
    }

    if type_set.contains(&Ty::Any) {
        return Ty::any();
    }

    if type_set.len() > 1 {
        type_set.retain(|ty| *ty != Ty::Unknown);
    }

    remove_redundant_primitive_intersection_types(arena, &mut type_set);

    let has_object_like_member = type_set
        .iter()
        .any(|ty| is_empty_object_intersection_identity_target(arena, *ty));
    if has_object_like_member {
        type_set.retain(
            |ty| !matches!(arena.type_data(*ty), TypeData::Object(object) if object.is_empty()),
        );
    }

    match type_set.as_slice() {
        [] => Ty::object(arena, []),
        [ty] => *ty,
        _ => arena.intern_intersection(type_set),
    }
}

fn add_type_to_intersection<'a>(
    arena: CheckerArena<'a>,
    type_set: &mut Vec<Ty<'a>>,
    seen_ids: &mut HashSet<TypeId>,
    ty: Ty<'a>,
) {
    if !seen_ids.insert(ty.id()) {
        return;
    }
    if let TypeData::Intersection(intersection) = arena.type_data(ty) {
        for ty in &intersection.types {
            add_type_to_intersection(arena, type_set, seen_ids, *ty);
        }
    } else {
        type_set.push(ty);
    }
}

fn is_empty_object_intersection_identity_target<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> bool {
    match arena.type_data(ty) {
        TypeData::Mapped(_) => true,
        TypeData::Object(object) => !object.is_empty(),
        _ => false,
    }
}

fn remove_redundant_primitive_intersection_types<'a>(
    arena: CheckerArena<'a>,
    type_set: &mut Vec<Ty<'a>>,
) {
    let has_string_literal = type_set.iter().any(|ty| {
        matches!(
            arena.type_data(*ty),
            TypeData::StringLiteral(_) | TypeData::TemplateLiteral(_)
        )
    });
    let has_number_literal = type_set
        .iter()
        .any(|ty| matches!(arena.type_data(*ty), TypeData::NumberLiteral(_)));
    let has_boolean_literal = type_set
        .iter()
        .any(|ty| matches!(arena.type_data(*ty), TypeData::BooleanLiteral(_)));
    let has_bigint_literal = type_set
        .iter()
        .any(|ty| matches!(arena.type_data(*ty), TypeData::BigIntLiteral(_)));

    type_set.retain(|ty| match arena.type_data(*ty) {
        TypeData::String => !has_string_literal,
        TypeData::Number => !has_number_literal,
        TypeData::Boolean => !has_boolean_literal,
        TypeData::Bigint => !has_bigint_literal,
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

fn remove_redundant_literal_types<'a>(arena: CheckerArena<'a>, type_set: &mut Vec<Ty<'a>>) {
    let has_string = type_set.contains(&Ty::String);
    let has_number = type_set.contains(&Ty::Number);
    let has_boolean = type_set.contains(&Ty::Boolean);
    let has_bigint = type_set.contains(&Ty::Bigint);
    let template_literals = (!has_string).then(|| {
        type_set
            .iter()
            .filter_map(|ty| match arena.type_data(*ty) {
                TypeData::TemplateLiteral(template_literal) => Some((*ty, template_literal)),
                _ => None,
            })
            .collect::<Vec<_>>()
    });

    type_set.retain(|ty| match arena.type_data(*ty) {
        TypeData::StringLiteral(string_literal) => {
            template_literals.as_ref().is_some_and(|templates| {
                !templates.iter().any(|(_, template_literal)| {
                    template_literal_matches_string(arena, template_literal, string_literal.value)
                })
            })
        }
        TypeData::TemplateLiteral(template_literal) => {
            template_literals.as_ref().is_some_and(|templates| {
                template_literal_static_value(template_literal).is_none_or(|value| {
                    !templates.iter().any(|(candidate_ty, candidate)| {
                        !arena.is_type_identical_to(*candidate_ty, *ty)
                            && template_literal_matches_string(arena, candidate, value)
                    })
                })
            })
        }
        TypeData::NumberLiteral(_) => !has_number,
        TypeData::BooleanLiteral(_) => !has_boolean,
        TypeData::BigIntLiteral(_) => !has_bigint,
        _ => true,
    });
}

fn reduce_boolean_literal_union<'a>(arena: CheckerArena<'a>, type_set: &mut Vec<Ty<'a>>) {
    let has_true = type_set
        .iter()
        .any(|ty| matches!(arena.type_data(*ty), TypeData::BooleanLiteral(true)));
    let has_false = type_set
        .iter()
        .any(|ty| matches!(arena.type_data(*ty), TypeData::BooleanLiteral(false)));
    if has_true && has_false {
        type_set.retain(|ty| !matches!(arena.type_data(*ty), TypeData::BooleanLiteral(_)));
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
    let mut seen = HashSet::new();
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
    seen: &mut HashSet<(usize, usize)>,
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

    match arena.type_data(*expression) {
        TypeData::String => {
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
        TypeData::StringLiteral(string_literal) => {
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
