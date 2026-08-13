use crate::{
    checker::{Checker, CheckerReturn},
    limits::ASSIGNABILITY_MAX_DEPTH,
    types::{CheckerArena, Ty, TyTypePredicate, TypeData},
};

impl<'a, 'store> CheckerReturn<'a, 'store> {
    pub(crate) fn is_assignable_to(&self, source: Ty<'a>, target: Ty<'a>) -> bool {
        self.is_assignable_to_at_depth(source, target, 0)
    }
}

pub(crate) fn is_assignable_to_without_checker<'a>(
    arena: CheckerArena<'a>,
    source: Ty<'a>,
    target: Ty<'a>,
) -> bool {
    is_assignable_to_at_depth_without_checker(arena, source, target, 0)
}

impl<'a, 'store> CheckerReturn<'a, 'store> {
    fn is_assignable_to_at_depth(&self, source: Ty<'a>, target: Ty<'a>, depth: usize) -> bool {
        if source == target {
            return true;
        }
        if depth >= ASSIGNABILITY_MAX_DEPTH {
            return false;
        }

        if matches!(self.arena().type_data(source), TypeData::GlobalThis) {
            let property_type = |name| {
                if name == "globalThis" {
                    Some(Ty::global_this())
                } else {
                    self.global_symbols
                        .global_this_value_symbol(name)
                        .map(|symbol| self.get_type_of_symbol(symbol))
                }
            };
            match self.arena().type_data(target) {
                TypeData::PrimitiveObject => return true,
                TypeData::Object(object) => {
                    return object.properties.iter().all(|property| {
                        property.optional
                            || (!property.computed
                                && property_type(property.name).is_some_and(|source_type| {
                                    self.is_assignable_to_at_depth(
                                        source_type,
                                        property.ty,
                                        depth + 1,
                                    )
                                }))
                    });
                }
                TypeData::Intersection(intersection) => {
                    return intersection
                        .types
                        .iter()
                        .all(|target| self.is_assignable_to_at_depth(source, *target, depth + 1));
                }
                _ => {}
            }
        }

        if let TypeData::Keyof(keyof) = self.arena().type_data(target)
            && matches!(self.arena().type_data(keyof.target), TypeData::GlobalThis)
            && !source.is_any_like(self.arena())
            && !source.is_never()
        {
            return match self.arena().type_data(source) {
                TypeData::Union(union) => union
                    .types
                    .iter()
                    .all(|source| self.is_assignable_to_at_depth(*source, target, depth + 1)),
                _ => property_name_from_key_type(self.arena(), source).is_some_and(|name| {
                    name == "globalThis"
                        || self.global_symbols.global_this_value_symbol(name).is_some()
                }),
            };
        }

        let references_match = matches!(
            (self.arena().type_data(source), self.arena().type_data(target)),
            (TypeData::TypeReference(source), TypeData::TypeReference(target))
                if source.has_identical_target(target)
                    && source.type_arguments.len() == target.type_arguments.len()
        );
        if !references_match {
            let expanded_source = self
                .expand_type_alias_for_relation(source, depth + 1)
                .unwrap_or(source);
            let expanded_target = self
                .expand_type_alias_for_relation(target, depth + 1)
                .unwrap_or(target);
            if expanded_source != source || expanded_target != target {
                return self.is_assignable_to_at_depth(expanded_source, expanded_target, depth + 1);
            }
        }

        is_assignable_to_at_depth(
            self.arena(),
            source,
            target,
            depth,
            |source, target, depth| self.is_assignable_to_at_depth(source, target, depth),
        )
    }
}

fn is_assignable_to_at_depth_without_checker<'a>(
    arena: CheckerArena<'a>,
    source: Ty<'a>,
    target: Ty<'a>,
    depth: usize,
) -> bool {
    is_assignable_to_at_depth(arena, source, target, depth, |source, target, depth| {
        is_assignable_to_at_depth_without_checker(arena, source, target, depth)
    })
}

fn is_assignable_to_at_depth<'a>(
    arena: CheckerArena<'a>,
    source: Ty<'a>,
    target: Ty<'a>,
    depth: usize,
    is_assignable_to_at_depth: impl Copy + Fn(Ty<'a>, Ty<'a>, usize) -> bool,
) -> bool {
    if source == target {
        return true;
    }
    if depth >= ASSIGNABILITY_MAX_DEPTH {
        return false;
    }

    let next_depth = depth + 1;

    match (arena.type_data(source), arena.type_data(target)) {
        // `never` is not assignable to any type
        (TypeData::Never, _) => true,
        // Nothing is assignable to `never`
        (_, TypeData::Never) => false,
        // `any` is assignable to any type and any type is assignable to `any`
        (_, TypeData::Any | TypeData::Error(_)) | (TypeData::Any | TypeData::Error(_), _) => true,
        // Any type is assignable to `unknown`
        (_, TypeData::Unknown) => true,
        // Unlike `any`, `unknown` is not assignable to any type (except for `any`)
        (TypeData::Unknown, _) => false,
        // `undefined` is assignable to `void`
        (TypeData::Undefined, TypeData::Void) => true,
        (TypeData::Object(source), TypeData::Object(target)) => properties_assignable_to(
            &source.properties,
            &target.properties,
            next_depth,
            is_assignable_to_at_depth,
        ),
        (TypeData::PrimitiveObject, TypeData::Object(target)) => properties_assignable_to(
            &[],
            &target.properties,
            next_depth,
            is_assignable_to_at_depth,
        ),
        (TypeData::Object(source), TypeData::PrimitiveObject) => properties_assignable_to(
            &source.properties,
            &[],
            next_depth,
            is_assignable_to_at_depth,
        ),
        (
            TypeData::Array(_)
            | TypeData::Tuple(_)
            | TypeData::Function(_)
            | TypeData::Mapped(_)
            | TypeData::ModuleNamespace(_),
            TypeData::PrimitiveObject,
        ) => true,
        (TypeData::ModuleNamespace(source), TypeData::Object(target)) => properties_assignable_to(
            &source.properties,
            &target.properties,
            next_depth,
            is_assignable_to_at_depth,
        ),
        (TypeData::Object(source), TypeData::ModuleNamespace(target)) => properties_assignable_to(
            &source.properties,
            &target.properties,
            next_depth,
            is_assignable_to_at_depth,
        ),
        (TypeData::ModuleNamespace(source), TypeData::ModuleNamespace(target)) => {
            properties_assignable_to(
                &source.properties,
                &target.properties,
                next_depth,
                is_assignable_to_at_depth,
            )
        }
        (TypeData::Union(source_union), _) => source_union
            .types
            .iter()
            .all(|source_type| is_assignable_to_at_depth(*source_type, target, next_depth)),
        (_, TypeData::Union(target_union)) => target_union
            .types
            .iter()
            .any(|target_type| is_assignable_to_at_depth(source, *target_type, next_depth)),
        (TypeData::Intersection(intersection), TypeData::Object(_)) => intersection
            .types
            .iter()
            .all(|ty| is_assignable_to_at_depth(target, *ty, next_depth)),
        (TypeData::Object(_), TypeData::Intersection(intersection)) => intersection
            .types
            .iter()
            .all(|ty| is_assignable_to_at_depth(source, *ty, next_depth)),
        (TypeData::Function(source), TypeData::Function(target)) => {
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
                && function_return_type_assignable_to(
                    source,
                    target,
                    next_depth,
                    is_assignable_to_at_depth,
                )
        }
        (TypeData::TypeReference(source), TypeData::TypeReference(target)) => {
            source.has_identical_target(target)
                && source.type_arguments.len() == target.type_arguments.len()
                && source
                    .type_arguments
                    .iter()
                    .zip(target.type_arguments.iter())
                    .all(|(source_argument, target_argument)| {
                        is_assignable_to_at_depth(*source_argument, *target_argument, next_depth)
                    })
        }
        (TypeData::TypeQuery(source), TypeData::TypeQuery(target)) => {
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
        (TypeData::TypeQuery(source), _) => {
            is_assignable_to_at_depth(source.resolved, target, next_depth)
        }
        (_, TypeData::TypeQuery(target)) => {
            is_assignable_to_at_depth(source, target.resolved, next_depth)
        }
        (TypeData::Array(source), TypeData::Array(target)) => {
            is_assignable_to_at_depth(source.element_type, target.element_type, next_depth)
        }
        (TypeData::Tuple(source), TypeData::Array(target)) => {
            source.elements.iter().all(|element| {
                is_assignable_to_at_depth(element.ty(), target.element_type, next_depth)
            })
        }
        (TypeData::Tuple(source), TypeData::Tuple(target)) => {
            source.elements.len() == target.elements.len()
                && source.elements.iter().zip(target.elements.iter()).all(
                    |(source_element, target_element)| {
                        tuple_element_assignable_to(
                            source_element,
                            target_element,
                            next_depth,
                            is_assignable_to_at_depth,
                        )
                    },
                )
        }
        (TypeData::UniqueSymbol(_), TypeData::Symbol) => true,
        (TypeData::NumberLiteral(_), TypeData::Number) => true,
        (TypeData::StringLiteral(_), TypeData::String) => true,
        (TypeData::StringLiteral(source), TypeData::StringLiteral(target)) => {
            source.value == target.value
        }
        (TypeData::BooleanLiteral(_), TypeData::Boolean) => true,
        (_, TypeData::Keyof(keyof)) => {
            is_assignable_to_keyof(arena, source, keyof.target, next_depth)
        }
        // Base case: if we can't find a more specific rule, we default to false but do so explicitly so that we can
        // catch any missing cases during development.
        (
            TypeData::Number
            | TypeData::String
            | TypeData::Bigint
            | TypeData::Boolean
            | TypeData::Null
            | TypeData::Undefined
            | TypeData::Void
            | TypeData::Symbol
            | TypeData::PrimitiveObject
            | TypeData::This
            | TypeData::GlobalThis
            | TypeData::BigIntLiteral(_)
            | TypeData::StringLiteral(_)
            | TypeData::NumberLiteral(_)
            | TypeData::TemplateLiteral(_)
            | TypeData::BooleanLiteral(_)
            | TypeData::Function(_)
            | TypeData::TypeReference(_)
            | TypeData::Array(_)
            | TypeData::Tuple(_)
            | TypeData::UniqueSymbol(_)
            | TypeData::Mapped(_)
            | TypeData::Object(_)
            | TypeData::Keyof(_)
            | TypeData::ModuleNamespace(_)
            | TypeData::Infer(_)
            | TypeData::Conditional(_)
            | TypeData::IndexedAccess(_)
            | TypeData::Intersection(_),
            _,
        ) => {
            // panic!("I don't know how to check assignability of\nsource: {source:?}\ntarget: {target:?}")
            false
        }
        (
            _,
            TypeData::Number
            | TypeData::String
            | TypeData::Bigint
            | TypeData::Boolean
            | TypeData::Null
            | TypeData::Undefined
            | TypeData::Void
            | TypeData::Symbol
            | TypeData::PrimitiveObject
            | TypeData::This
            | TypeData::GlobalThis
            | TypeData::BigIntLiteral(_)
            | TypeData::StringLiteral(_)
            | TypeData::NumberLiteral(_)
            | TypeData::TemplateLiteral(_)
            | TypeData::BooleanLiteral(_)
            | TypeData::Function(_)
            | TypeData::TypeReference(_)
            | TypeData::Array(_)
            | TypeData::Tuple(_)
            | TypeData::UniqueSymbol(_)
            | TypeData::Mapped(_)
            | TypeData::Object(_)
            | TypeData::ModuleNamespace(_)
            | TypeData::Infer(_)
            | TypeData::Conditional(_)
            | TypeData::IndexedAccess(_),
        ) => {
            // panic!("I don't know how to check assignability of\nsource: {source:?}\ntarget: {target:?}")
            false
        }
        (TypeData::None, _) => false,
    }
}

fn is_assignable_to_keyof<'a>(
    arena: CheckerArena<'a>,
    source: Ty<'a>,
    target: Ty<'a>,
    depth: usize,
) -> bool {
    let Some(source_name) = property_name_from_key_type(arena, source) else {
        return false;
    };
    keyof_type_contains_property(arena, target, source_name, depth)
}

fn property_name_from_key_type<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> Option<&'a str> {
    match arena.type_data(ty) {
        TypeData::StringLiteral(literal) => Some(literal.value),
        TypeData::NumberLiteral(literal) => literal.raw.as_ref().map(oxc_str::Str::as_str),
        TypeData::BooleanLiteral(true) => Some("true"),
        TypeData::BooleanLiteral(false) => Some("false"),
        _ => None,
    }
}

fn keyof_type_contains_property<'a>(
    arena: CheckerArena<'a>,
    target: Ty<'a>,
    name: &str,
    depth: usize,
) -> bool {
    if depth >= ASSIGNABILITY_MAX_DEPTH {
        return false;
    }

    match arena.type_data(target) {
        TypeData::Object(object) => object
            .properties
            .iter()
            .any(|property| !property.computed && property.name == name),
        TypeData::Intersection(intersection) => intersection
            .types
            .iter()
            .any(|ty| keyof_type_contains_property(arena, *ty, name, depth + 1)),
        _ => false,
    }
}

fn tuple_element_assignable_to<'a>(
    source: &crate::types::TupleElement<'a>,
    target: &crate::types::TupleElement<'a>,
    depth: usize,
    is_assignable_to_at_depth: impl Copy + Fn(Ty<'a>, Ty<'a>, usize) -> bool,
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
    is_assignable_to_at_depth: impl Copy + Fn(Ty<'a>, Ty<'a>, usize) -> bool,
) -> bool {
    match target.type_predicate {
        Some(target_predicate) => source.type_predicate.is_some_and(|source_predicate| {
            type_predicate_assignable_to(
                source_predicate,
                target_predicate,
                depth,
                is_assignable_to_at_depth,
            )
        }),
        None => is_assignable_to_at_depth(source.return_type, target.return_type, depth),
    }
}

fn type_predicate_assignable_to<'a>(
    source: &TyTypePredicate<'a>,
    target: &TyTypePredicate<'a>,
    depth: usize,
    is_assignable_to_at_depth: impl Copy + Fn(Ty<'a>, Ty<'a>, usize) -> bool,
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
    is_assignable_to_at_depth: impl Copy + Fn(Ty<'a>, Ty<'a>, usize) -> bool,
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
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let is_assignable_to =
            |source, target| is_assignable_to_without_checker(arena, source, target);

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
        let is_assignable_to =
            |source, target| is_assignable_to_without_checker(arena, source, target);

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
        let is_assignable_to =
            |source, target| is_assignable_to_without_checker(arena, source, target);

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
        let is_assignable_to =
            |source, target| is_assignable_to_without_checker(arena, source, target);

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
