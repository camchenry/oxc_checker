use std::collections::HashSet;

use crate::{
    TyIntersection,
    types::{CheckerArena, Ty, TyTemplateLiteral, TyUnion},
};

pub fn reduce_union_type<'a>(
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
    reduce_boolean_literal_union(&mut type_set);

    if type_set.len() > 1 {
        type_set.retain(|ty| !ty.is_never());
    }

    // TODO(perf): this is just for nicer display purposes but we
    // should handle this when printing instead, with flags?
    normalize_null_undefined_order(&mut type_set);

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

pub(crate) fn reduce_intersection_type<'a>(
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

fn normalize_null_undefined_order(type_set: &mut [Ty<'_>]) {
    let Some(null_index) = type_set.iter().position(|ty| matches!(ty, Ty::Null)) else {
        return;
    };
    let Some(undefined_index) = type_set.iter().position(|ty| matches!(ty, Ty::Undefined)) else {
        return;
    };
    if undefined_index < null_index {
        type_set.swap(undefined_index, null_index);
    }
}

fn remove_redundant_literal_types(type_set: &mut Vec<Ty<'_>>) {
    let has_string = type_set.iter().any(|ty| matches!(ty, Ty::String));
    let has_number = type_set.iter().any(|ty| matches!(ty, Ty::Number));
    let has_boolean = type_set.iter().any(|ty| matches!(ty, Ty::Boolean));
    let has_bigint = type_set.iter().any(|ty| matches!(ty, Ty::Bigint));
    let template_literals = (!has_string).then(|| {
        type_set
            .iter()
            .filter_map(|ty| match ty {
                Ty::TemplateLiteral(template_literal) => Some(*template_literal),
                _ => None,
            })
            .collect::<Vec<_>>()
    });

    type_set.retain(|ty| match ty {
        Ty::StringLiteral(string_literal) => template_literals.as_ref().is_some_and(|templates| {
            !templates.iter().any(|template_literal| {
                template_literal_matches_string(template_literal, string_literal.value)
            })
        }),
        Ty::TemplateLiteral(template_literal) => {
            template_literals.as_ref().is_some_and(|templates| {
                template_literal_static_value(template_literal).is_none_or(|value| {
                    !templates.iter().any(|candidate| {
                        *candidate != *template_literal
                            && template_literal_matches_string(candidate, value)
                    })
                })
            })
        }
        Ty::NumberLiteral(_) => !has_number,
        Ty::BooleanLiteral(_) => !has_boolean,
        Ty::BigIntLiteral(_) => !has_bigint,
        _ => true,
    });
}

fn reduce_boolean_literal_union(type_set: &mut Vec<Ty<'_>>) {
    let has_true = type_set
        .iter()
        .any(|ty| matches!(ty, Ty::BooleanLiteral(true)));
    let has_false = type_set
        .iter()
        .any(|ty| matches!(ty, Ty::BooleanLiteral(false)));
    if has_true && has_false {
        type_set.retain(|ty| !matches!(ty, Ty::BooleanLiteral(_)));
        if !type_set.iter().any(|ty| matches!(ty, Ty::Boolean)) {
            type_set.push(Ty::Boolean);
        }
    }
}

fn template_literal_matches_string(template_literal: &TyTemplateLiteral<'_>, value: &str) -> bool {
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
        template_literal,
        0,
        value,
        first_quasi.value.len(),
        &mut seen,
    )
}

fn template_literal_remaining_matches(
    template_literal: &TyTemplateLiteral<'_>,
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

    match expression {
        Ty::String => {
            if next_quasi.is_empty() {
                return string_split_indices(&value[offset..]).any(|split_index| {
                    template_literal_remaining_matches(
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
        Ty::StringLiteral(string_literal) => {
            let Some(remaining) = value[offset..].strip_prefix(string_literal.value) else {
                return false;
            };
            let Some(remaining) = remaining.strip_prefix(next_quasi) else {
                return false;
            };
            template_literal_remaining_matches(
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
