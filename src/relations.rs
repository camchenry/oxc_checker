use crate::types::{Ty, TyTypePredicate};

const ASSIGNABILITY_MAX_DEPTH: usize = 128;

pub(crate) fn is_assignable_to<'a>(source: Ty<'a>, target: Ty<'a>) -> bool {
    is_assignable_to_at_depth(source, target, 0)
}

fn is_assignable_to_at_depth<'a>(source: Ty<'a>, target: Ty<'a>, depth: usize) -> bool {
    if source == target {
        return true;
    }
    if depth >= ASSIGNABILITY_MAX_DEPTH {
        return false;
    }

    let next_depth = depth + 1;

    match (source, target) {
        (_, Ty::Any | Ty::Unknown) | (Ty::Any, _) => true,
        (Ty::Object(source), Ty::Object(target)) => {
            properties_assignable_to(&source.properties, &target.properties, next_depth)
        }
        (Ty::ModuleNamespace(source), Ty::Object(target)) => {
            properties_assignable_to(&source.properties, &target.properties, next_depth)
        }
        (Ty::Object(source), Ty::ModuleNamespace(target)) => {
            properties_assignable_to(&source.properties, &target.properties, next_depth)
        }
        (Ty::ModuleNamespace(source), Ty::ModuleNamespace(target)) => {
            properties_assignable_to(&source.properties, &target.properties, next_depth)
        }
        (Ty::Union(source), target) => source
            .types
            .iter()
            .all(|source_type| is_assignable_to_at_depth(*source_type, target, next_depth)),
        (source, Ty::Union(target)) => target
            .types
            .iter()
            .any(|target_type| is_assignable_to_at_depth(source, *target_type, next_depth)),
        (Ty::Function(source), Ty::Function(target)) => {
            source.parameters.len() == target.parameters.len()
                && source.parameters.iter().zip(target.parameters.iter()).all(
                    |(source_parameter, target_parameter)| {
                        is_assignable_to_at_depth(
                            target_parameter.ty,
                            source_parameter.ty,
                            next_depth,
                        )
                    },
                )
                && function_return_type_assignable_to(source, target, next_depth)
        }
        (Ty::TypeReference(source), Ty::TypeReference(target)) => {
            source.name == target.name
                && source.type_arguments.len() == target.type_arguments.len()
                && source
                    .type_arguments
                    .iter()
                    .zip(target.type_arguments.iter())
                    .all(|(source_argument, target_argument)| {
                        is_assignable_to_at_depth(*source_argument, *target_argument, next_depth)
                    })
        }
        (Ty::TypeQuery(source), Ty::TypeQuery(target)) => {
            source.name == target.name
                && source.type_arguments.len() == target.type_arguments.len()
                && source
                    .type_arguments
                    .iter()
                    .zip(target.type_arguments.iter())
                    .all(|(source_argument, target_argument)| {
                        is_assignable_to_at_depth(*source_argument, *target_argument, next_depth)
                    })
        }
        // A `typeof X` query is transparently compatible with whatever the queried symbol's type allows.
        (Ty::TypeQuery(source), _) => {
            is_assignable_to_at_depth(source.resolved, target, next_depth)
        }
        (_, Ty::TypeQuery(target)) => {
            is_assignable_to_at_depth(source, target.resolved, next_depth)
        }
        (Ty::Array(source), Ty::Array(target)) => {
            is_assignable_to_at_depth(source.element_type, target.element_type, next_depth)
        }
        (Ty::Tuple(source), Ty::Array(target)) => source.elements.iter().all(|element| {
            is_assignable_to_at_depth(element.ty(), target.element_type, next_depth)
        }),
        (Ty::Tuple(source), Ty::Tuple(target)) => {
            source.elements.len() == target.elements.len()
                && source.elements.iter().zip(target.elements.iter()).all(
                    |(source_element, target_element)| {
                        tuple_element_assignable_to(source_element, target_element, next_depth)
                    },
                )
        }
        (Ty::UniqueSymbol(_), Ty::Symbol) => true,
        (Ty::NumberLiteral(_), Ty::Number) => true,
        (Ty::StringLiteral(_), Ty::String) => true,
        (Ty::StringLiteral(source), Ty::StringLiteral(target)) => {
            string_literal_type_to_property_name(source.value)
                == string_literal_type_to_property_name(target.value)
        }
        (Ty::BooleanLiteral(_), Ty::Boolean) => true,
        (source, Ty::Keyof(target)) => is_assignable_to_keyof(source, target.target, next_depth),
        _ => false,
    }
}

fn is_assignable_to_keyof<'a>(source: Ty<'a>, target: Ty<'a>, depth: usize) -> bool {
    let Some(source_name) = property_name_from_key_type(source) else {
        return false;
    };
    keyof_type_contains_property(target, source_name, depth)
}

fn property_name_from_key_type(ty: Ty<'_>) -> Option<&str> {
    match ty {
        Ty::StringLiteral(literal) => Some(string_literal_type_to_property_name(literal.value)),
        Ty::NumberLiteral(literal) => Some(literal.value),
        Ty::BooleanLiteral(true) => Some("true"),
        Ty::BooleanLiteral(false) => Some("false"),
        _ => None,
    }
}

// TODO: There is a better way to do this. We should avoid storing the quotes
// in the string literal type to begin with.
fn string_literal_type_to_property_name(value: &str) -> &str {
    if value.len() >= 2
        && ((value.starts_with('"') && value.ends_with('"'))
            || (value.starts_with('\'') && value.ends_with('\'')))
    {
        &value[1..value.len() - 1]
    } else {
        value
    }
}

fn keyof_type_contains_property(target: Ty<'_>, name: &str, depth: usize) -> bool {
    if depth >= ASSIGNABILITY_MAX_DEPTH {
        return false;
    }

    match target {
        Ty::Object(object) => object
            .properties
            .iter()
            .any(|property| !property.computed && property.name == name),
        Ty::Intersection(intersection) => intersection
            .types
            .iter()
            .any(|ty| keyof_type_contains_property(*ty, name, depth + 1)),
        _ => false,
    }
}

fn tuple_element_assignable_to<'a>(
    source: &crate::types::TupleElement<'a>,
    target: &crate::types::TupleElement<'a>,
    depth: usize,
) -> bool {
    use crate::types::TupleElement;

    match (source, target) {
        (TupleElement::Regular(source), TupleElement::Regular(target))
        | (TupleElement::Rest(source), TupleElement::Rest(target))
        | (TupleElement::Optional(source), TupleElement::Optional(target)) => {
            is_assignable_to_at_depth(*source, *target, depth)
        }
        _ => false,
    }
}

fn function_return_type_assignable_to<'a>(
    source: &crate::types::TyFunction<'a>,
    target: &crate::types::TyFunction<'a>,
    depth: usize,
) -> bool {
    match target.type_predicate {
        Some(target_predicate) => source.type_predicate.is_some_and(|source_predicate| {
            type_predicate_assignable_to(source_predicate, target_predicate, depth)
        }),
        None => is_assignable_to_at_depth(source.return_type, target.return_type, depth),
    }
}

fn type_predicate_assignable_to<'a>(
    source: &TyTypePredicate<'a>,
    target: &TyTypePredicate<'a>,
    depth: usize,
) -> bool {
    crate::types::type_predicate_kinds_match(source, target)
        && match (source.target_type, target.target_type) {
            (Some(source_type), Some(target_type)) => {
                is_assignable_to_at_depth(source_type, target_type, depth)
            }
            (None, None) => true,
            _ => false,
        }
}

fn properties_assignable_to<'a>(
    source_properties: &[crate::types::TyProperty<'a>],
    target_properties: &[crate::types::TyProperty<'a>],
    depth: usize,
) -> bool {
    target_properties.iter().all(|target_property| {
        let Some(source_property) = source_properties.iter().find(|source_property| {
            source_property.name == target_property.name
                && source_property.computed == target_property.computed
        }) else {
            return target_property.optional;
        };

        if source_property.optional
            && !target_property.optional
            && !is_assignable_to_at_depth(Ty::undefined(), target_property.ty, depth)
        {
            return false;
        }

        is_assignable_to_at_depth(source_property.ty, target_property.ty, depth)
    })
}
