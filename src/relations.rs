use crate::{
    limits::ASSIGNABILITY_MAX_DEPTH,
    types::{Ty, TyTypePredicate},
};

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
        // `never` is not assignable to any type
        (Ty::Never, _) => true,
        // Nothing is assignable to `never`
        (_, Ty::Never) => false,
        // `any` is assignable to any type and any type is assignable to `any`
        (_, Ty::Any) | (Ty::Any, _) => true,
        // Any type is assignable to `unknown`
        (_, Ty::Unknown) => true,
        // Unlike `any`, `unknown` is not assignable to any type (except for `any`)
        (Ty::Unknown, _) => false,
        // `undefined` is assignable to `void`
        (Ty::Undefined, Ty::Void) => true,
        (Ty::Object(source), Ty::Object(target)) => {
            properties_assignable_to(&source.properties, &target.properties, next_depth)
        }
        (Ty::PrimitiveObject, Ty::Object(target)) => {
            properties_assignable_to(&[], &target.properties, next_depth)
        }
        (Ty::Object(source), Ty::PrimitiveObject) => {
            properties_assignable_to(&source.properties, &[], next_depth)
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
        (Ty::Intersection(_), _) => {
            /* TODO: Implement */
            false
        }
        (_, Ty::Intersection(_)) => {
            /* TODO: Implement */
            false
        }
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
        // Base case: if we can't find a more specific rule, we default to false but do so explicitly so that we can
        // catch any missing cases during development.
        (
            Ty::Number
            | Ty::String
            | Ty::Bigint
            | Ty::Boolean
            | Ty::Null
            | Ty::Undefined
            | Ty::Void
            | Ty::Symbol
            | Ty::PrimitiveObject
            | Ty::This
            | Ty::BigIntLiteral(_)
            | Ty::StringLiteral(_)
            | Ty::NumberLiteral(_)
            | Ty::TemplateLiteral(_)
            | Ty::BooleanLiteral(_)
            | Ty::Function(_)
            | Ty::TypeReference(_)
            | Ty::Array(_)
            | Ty::Tuple(_)
            | Ty::UniqueSymbol(_)
            | Ty::Mapped(_)
            | Ty::Object(_)
            | Ty::Keyof(_)
            | Ty::ModuleNamespace(_)
            | Ty::Infer(_)
            | Ty::Conditional(_)
            | Ty::IndexedAccess(_),
            _,
        ) => false,
        (
            _,
            Ty::Number
            | Ty::String
            | Ty::Bigint
            | Ty::Boolean
            | Ty::Null
            | Ty::Undefined
            | Ty::Void
            | Ty::Symbol
            | Ty::PrimitiveObject
            | Ty::This
            | Ty::BigIntLiteral(_)
            | Ty::StringLiteral(_)
            | Ty::NumberLiteral(_)
            | Ty::TemplateLiteral(_)
            | Ty::BooleanLiteral(_)
            | Ty::Function(_)
            | Ty::TypeReference(_)
            | Ty::Array(_)
            | Ty::Tuple(_)
            | Ty::UniqueSymbol(_)
            | Ty::Mapped(_)
            | Ty::Object(_)
            | Ty::ModuleNamespace(_)
            | Ty::Infer(_)
            | Ty::Conditional(_)
            | Ty::IndexedAccess(_),
        ) => false,
        (Ty::None, _) => false,
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
        Ty::NumberLiteral(literal) => literal.raw.as_ref().map(|s| s.as_str()),
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

#[cfg(test)]
mod tests {
    use oxc_allocator::Allocator;

    use crate::CheckerArena;

    use super::*;

    #[test]
    fn test_any_unknown_object_void_undefined_null_never_assignability() {
        // All types are assignable to themselves.
        assert!(is_assignable_to(Ty::any(), Ty::any()));
        assert!(is_assignable_to(Ty::unknown(), Ty::unknown()));
        assert!(is_assignable_to(
            Ty::primitive_object(),
            Ty::primitive_object()
        ));
        assert!(is_assignable_to(Ty::void(), Ty::void()));
        assert!(is_assignable_to(Ty::undefined(), Ty::undefined()));
        assert!(is_assignable_to(Ty::null(), Ty::null()));
        assert!(is_assignable_to(Ty::never(), Ty::never()));
        // `any` is assignable to all types, except for `never`
        assert!(is_assignable_to(Ty::any(), Ty::unknown()));
        assert!(is_assignable_to(Ty::any(), Ty::primitive_object()));
        assert!(is_assignable_to(Ty::any(), Ty::void()));
        assert!(is_assignable_to(Ty::any(), Ty::undefined()));
        assert!(is_assignable_to(Ty::any(), Ty::null()));
        assert!(!is_assignable_to(Ty::any(), Ty::never()));
        // `unknown` is basically the same as `any`, but doesn't allow for any type to be assigned to it
        assert!(is_assignable_to(Ty::unknown(), Ty::any()));
        assert!(!is_assignable_to(Ty::unknown(), Ty::primitive_object()));
        assert!(!is_assignable_to(Ty::unknown(), Ty::void()));
        assert!(!is_assignable_to(Ty::unknown(), Ty::undefined()));
        assert!(!is_assignable_to(Ty::unknown(), Ty::null()));
        assert!(!is_assignable_to(Ty::unknown(), Ty::never()));
        // `object` is assignable to `any`, `unknown`, and itself, but not to `void`, `undefined`, `null`, or `never`
        assert!(is_assignable_to(Ty::primitive_object(), Ty::any()));
        assert!(is_assignable_to(Ty::primitive_object(), Ty::unknown()));
        assert!(!is_assignable_to(Ty::primitive_object(), Ty::void()));
        assert!(!is_assignable_to(Ty::primitive_object(), Ty::undefined()));
        assert!(!is_assignable_to(Ty::primitive_object(), Ty::null()));
        assert!(!is_assignable_to(Ty::primitive_object(), Ty::never()));
        // `void` is not assignable to anything, except for `any` and `unknown`
        assert!(is_assignable_to(Ty::void(), Ty::any()));
        assert!(is_assignable_to(Ty::void(), Ty::unknown()));
        assert!(!is_assignable_to(Ty::void(), Ty::primitive_object()));
        assert!(!is_assignable_to(Ty::void(), Ty::undefined()));
        assert!(!is_assignable_to(Ty::void(), Ty::null()));
        assert!(!is_assignable_to(Ty::void(), Ty::never()));
        // `undefined` is not assignable to anything, except for `any`, `unknown`, and `void`
        assert!(is_assignable_to(Ty::undefined(), Ty::any()));
        assert!(is_assignable_to(Ty::undefined(), Ty::unknown()));
        assert!(is_assignable_to(Ty::undefined(), Ty::void()));
        assert!(!is_assignable_to(Ty::undefined(), Ty::primitive_object()));
        assert!(!is_assignable_to(Ty::undefined(), Ty::null()));
        assert!(!is_assignable_to(Ty::undefined(), Ty::never()));
        // `null` is not assignable to anything, except for `any` and `unknown`
        assert!(is_assignable_to(Ty::null(), Ty::any()));
        assert!(is_assignable_to(Ty::null(), Ty::unknown()));
        assert!(!is_assignable_to(Ty::null(), Ty::primitive_object()));
        assert!(!is_assignable_to(Ty::null(), Ty::void()));
        assert!(!is_assignable_to(Ty::null(), Ty::undefined()));
        assert!(!is_assignable_to(Ty::null(), Ty::never()));
        // `never` is assignable to everything
        assert!(is_assignable_to(Ty::never(), Ty::any()));
        assert!(is_assignable_to(Ty::never(), Ty::unknown()));
        assert!(is_assignable_to(Ty::never(), Ty::primitive_object()));
        assert!(is_assignable_to(Ty::never(), Ty::void()));
        assert!(is_assignable_to(Ty::never(), Ty::undefined()));
        assert!(is_assignable_to(Ty::never(), Ty::null()));
    }

    #[test]
    fn test_intersection_assignability() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);

        let number_and_string = Ty::intersection(
            arena,
            [
                Ty::object(arena, [Ty::property("a", Ty::number())]),
                Ty::object(arena, [Ty::property("b", Ty::string())]),
            ],
        );

        // { a: number, b: string } -> { a: number } & { b: string }
        assert!(is_assignable_to(
            Ty::object(
                arena,
                [
                    Ty::property("a", Ty::number()),
                    Ty::property("b", Ty::string())
                ]
            ),
            number_and_string
        ));
        // { a: number } -!> { a: number, b: string }
        assert!(!is_assignable_to(
            Ty::object(arena, [Ty::property("a", Ty::number())]),
            Ty::object(
                arena,
                [
                    Ty::property("a", Ty::number()),
                    Ty::property("b", Ty::string())
                ]
            ),
        ));
        // { a: number } & { b: string } -> { a: number, b: string }
        assert!(is_assignable_to(
            number_and_string,
            Ty::object(
                arena,
                [
                    Ty::property("a", Ty::number()),
                    Ty::property("b", Ty::string())
                ]
            ),
        ));
    }

    #[test]
    fn object_type_assignability() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);

        // { a: number, b: string } is assignable to { a: number }
        assert!(is_assignable_to(
            Ty::object(
                arena,
                [
                    Ty::property("a", Ty::number()),
                    Ty::property("b", Ty::string())
                ]
            ),
            Ty::object(arena, [Ty::property("a", Ty::number())])
        ));

        // { a: number } is not assignable to { a: number, b: string }
        assert!(!is_assignable_to(
            Ty::object(arena, [Ty::property("a", Ty::number())]),
            Ty::object(
                arena,
                [
                    Ty::property("a", Ty::number()),
                    Ty::property("b", Ty::string())
                ]
            ),
        ));

        // { a: number, b: string } is assignable to {}
        assert!(is_assignable_to(
            Ty::object(
                arena,
                [
                    Ty::property("a", Ty::number()),
                    Ty::property("b", Ty::string())
                ]
            ),
            Ty::object(arena, [])
        ));
    }

    #[test]
    fn test_primitive_object_type_assignability() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);

        // primitive object is assignable to itself
        assert!(is_assignable_to(
            Ty::primitive_object(),
            Ty::primitive_object()
        ));
        // `object` is assignable to {}
        assert!(is_assignable_to(
            Ty::primitive_object(),
            Ty::object(arena, [])
        ));
        // `{}` is assignable to `object`
        assert!(is_assignable_to(
            Ty::object(arena, []),
            Ty::primitive_object()
        ));
        // `{}` is not assignable to undefined, null
        assert!(!is_assignable_to(Ty::object(arena, []), Ty::undefined()));
        assert!(!is_assignable_to(Ty::object(arena, []), Ty::null()));
    }
}
