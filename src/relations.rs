use crate::{
    TupleElement, TyProperty,
    checker::Checker,
    limits::ASSIGNABILITY_MAX_DEPTH,
    type_predicate_kinds_match,
    types::{Ty, TyKind},
};

impl<'a, 'store> Checker<'a, 'store> {
    pub fn is_assignable_to(&self, source: Ty<'a>, target: Ty<'a>) -> bool {
        self.is_assignable_to_at_depth(source, target, 0)
    }

    fn is_assignable_to_at_depth(&self, source: Ty<'a>, target: Ty<'a>, depth: usize) -> bool {
        if source == target {
            return true;
        }
        if depth >= ASSIGNABILITY_MAX_DEPTH {
            return false;
        }

        if matches!(self.ty_kind(source), TyKind::GlobalThis) {
            let property_type = |name| {
                if name == "globalThis" {
                    Some(Ty::global_this())
                } else {
                    self.global_symbols
                        .global_this_value_symbol(name)
                        .map(|symbol| {
                            self.apparent_type_for_conditional_match(
                                symbol.program_id,
                                self.get_type_of_symbol(symbol),
                                depth + 1,
                            )
                        })
                }
            };
            match self.ty_kind(target) {
                TyKind::PrimitiveObject => return true,
                TyKind::Object(object) => {
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
                TyKind::Intersection(intersection) => {
                    return intersection
                        .types
                        .iter()
                        .all(|target| self.is_assignable_to_at_depth(source, *target, depth + 1));
                }
                _ => {}
            }
        }

        if let TyKind::Keyof(keyof) = self.ty_kind(target)
            && matches!(self.ty_kind(keyof.target), TyKind::GlobalThis)
            && !source.is_any_like(self.arena())
            && !source.is_never()
        {
            return match self.ty_kind(source) {
                TyKind::Union(union) => union
                    .types
                    .iter()
                    .all(|source| self.is_assignable_to_at_depth(*source, target, depth + 1)),
                _ => self
                    .property_name_from_key_type(source)
                    .is_some_and(|name| {
                        name == "globalThis"
                            || self.global_symbols.global_this_value_symbol(name).is_some()
                    }),
            };
        }

        let references_match = matches!(
            (self.ty_kind(source), self.ty_kind(target)),
            (TyKind::TypeReference(source), TyKind::TypeReference(target))
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

        let next_depth = depth + 1;

        match (self.ty_kind(source), self.ty_kind(target)) {
            // `never` is not assignable to any type
            (TyKind::Never, _) => true,
            // Nothing is assignable to `never`
            (_, TyKind::Never) => false,
            // `any` is assignable to any type and any type is assignable to `any`
            (_, TyKind::Any | TyKind::Error(_)) | (TyKind::Any | TyKind::Error(_), _) => true,
            // Any type is assignable to `unknown`
            (_, TyKind::Unknown) => true,
            // Unlike `any`, `unknown` is not assignable to any type (except for `any`)
            (TyKind::Unknown, _) => false,
            // `undefined` is assignable to `void`
            (TyKind::Undefined, TyKind::Void) => true,
            (TyKind::Object(source), TyKind::Object(target)) => {
                self.properties_assignable_to(source.properties, target.properties, next_depth)
            }
            (TyKind::PrimitiveObject, TyKind::Object(target)) => {
                self.properties_assignable_to(&[], target.properties, next_depth)
            }
            (TyKind::Object(source), TyKind::PrimitiveObject) => {
                self.properties_assignable_to(source.properties, &[], next_depth)
            }
            (
                TyKind::Array(_)
                | TyKind::Tuple(_)
                | TyKind::Function(_)
                | TyKind::Mapped(_)
                | TyKind::ModuleNamespace(_),
                TyKind::PrimitiveObject,
            ) => true,
            (TyKind::ModuleNamespace(source), TyKind::Object(target)) => {
                self.properties_assignable_to(&source.properties, target.properties, next_depth)
            }
            (TyKind::Object(source), TyKind::ModuleNamespace(target)) => {
                self.properties_assignable_to(source.properties, &target.properties, next_depth)
            }
            (TyKind::ModuleNamespace(source), TyKind::ModuleNamespace(target)) => {
                self.properties_assignable_to(&source.properties, &target.properties, next_depth)
            }
            (TyKind::Union(source_union), _) => source_union.types.iter().all(|source_type| {
                self.is_assignable_to_at_depth(*source_type, target, next_depth)
            }),
            (_, TyKind::Union(target_union)) => target_union.types.iter().any(|target_type| {
                self.is_assignable_to_at_depth(source, *target_type, next_depth)
            }),
            (TyKind::Intersection(intersection), TyKind::Object(_)) => intersection
                .types
                .iter()
                .all(|ty| self.is_assignable_to_at_depth(target, *ty, next_depth)),
            (TyKind::Object(_), TyKind::Intersection(intersection)) => intersection
                .types
                .iter()
                .all(|ty| self.is_assignable_to_at_depth(source, *ty, next_depth)),
            (TyKind::Function(source), TyKind::Function(target)) => {
                source.parameters.len() == target.parameters.len()
                    && source.parameters.iter().zip(target.parameters.iter()).all(
                        |(source_parameter, target_parameter)| {
                            self.is_assignable_to_at_depth(
                                target_parameter.ty,
                                source_parameter.ty,
                                next_depth,
                            )
                        },
                    )
                    && match target.type_predicate {
                        Some(target_predicate) => {
                            source.type_predicate.is_some_and(|source_predicate| {
                                type_predicate_kinds_match(source_predicate, target_predicate)
                                    && match (
                                        source_predicate.target_type(),
                                        target_predicate.target_type(),
                                    ) {
                                        (Some(source_type), Some(target_type)) => self
                                            .is_assignable_to_at_depth(
                                                source_type,
                                                target_type,
                                                next_depth,
                                            ),
                                        (None, None) => true,
                                        _ => false,
                                    }
                            })
                        }
                        None => self.is_assignable_to_at_depth(
                            source.return_type,
                            target.return_type,
                            next_depth,
                        ),
                    }
            }
            (TyKind::TypeReference(source), TyKind::TypeReference(target)) => {
                source.has_identical_target(target)
                    && self.type_arguments_assignable_to(
                        &source.type_arguments,
                        &target.type_arguments,
                        next_depth,
                    )
            }
            (TyKind::TypeQuery(source), TyKind::TypeQuery(target)) => {
                source.name == target.name
                    && self.type_arguments_assignable_to(
                        &source.type_arguments,
                        &target.type_arguments,
                        next_depth,
                    )
            }
            // A `typeof X` query is transparently compatible with whatever the queried symbol's type allows.
            (TyKind::TypeQuery(source), _) => {
                self.is_assignable_to_at_depth(source.resolved, target, next_depth)
            }
            (_, TyKind::TypeQuery(target)) => {
                self.is_assignable_to_at_depth(source, target.resolved, next_depth)
            }
            (TyKind::Array(source), TyKind::Array(target)) => {
                self.is_assignable_to_at_depth(source.element_type, target.element_type, next_depth)
            }
            (TyKind::Tuple(source), TyKind::Array(target)) => {
                source.elements.iter().all(|element| {
                    self.is_assignable_to_at_depth(element.ty(), target.element_type, next_depth)
                })
            }
            (TyKind::Tuple(source), TyKind::Tuple(target)) => {
                source.elements.len() == target.elements.len()
                    && source.elements.iter().zip(target.elements.iter()).all(
                        |(source_element, target_element)| match (source_element, target_element) {
                            (TupleElement::Regular(source), TupleElement::Regular(target))
                            | (TupleElement::Rest(source), TupleElement::Rest(target))
                            | (TupleElement::Optional(source), TupleElement::Optional(target)) => {
                                self.is_assignable_to_at_depth(*source, *target, next_depth)
                            }
                            _ => false,
                        },
                    )
            }
            (TyKind::UniqueSymbol(_), TyKind::Symbol) => true,
            (TyKind::NumberLiteral(_), TyKind::Number) => true,
            (TyKind::StringLiteral(_), TyKind::String) => true,
            (TyKind::StringLiteral(source), TyKind::StringLiteral(target)) => {
                source.value == target.value
            }
            (TyKind::BooleanLiteral(_), TyKind::Boolean) => true,
            (_, TyKind::Keyof(keyof)) => {
                let Some(source_name) = self.property_name_from_key_type(source) else {
                    return false;
                };
                self.keyof_type_contains_property(keyof.target, source_name, next_depth)
            }
            // Base case: if we can't find a more specific rule, we default to false but do so explicitly so that we can
            // catch any missing cases during development.
            (
                TyKind::Number
                | TyKind::String
                | TyKind::Bigint
                | TyKind::Boolean
                | TyKind::Null
                | TyKind::Undefined
                | TyKind::Void
                | TyKind::Symbol
                | TyKind::PrimitiveObject
                | TyKind::This
                | TyKind::GlobalThis
                | TyKind::BigIntLiteral(_)
                | TyKind::StringLiteral(_)
                | TyKind::NumberLiteral(_)
                | TyKind::TemplateLiteral(_)
                | TyKind::BooleanLiteral(_)
                | TyKind::Function(_)
                | TyKind::TypeReference(_)
                | TyKind::Array(_)
                | TyKind::Tuple(_)
                | TyKind::UniqueSymbol(_)
                | TyKind::Mapped(_)
                | TyKind::Object(_)
                | TyKind::Keyof(_)
                | TyKind::ModuleNamespace(_)
                | TyKind::Infer(_)
                | TyKind::Conditional(_)
                | TyKind::IndexedAccess(_)
                | TyKind::Intersection(_),
                _,
            ) => {
                // panic!("I don't know how to check assignability of\nsource: {source:?}\ntarget: {target:?}")
                false
            }
            (
                _,
                TyKind::Number
                | TyKind::String
                | TyKind::Bigint
                | TyKind::Boolean
                | TyKind::Null
                | TyKind::Undefined
                | TyKind::Void
                | TyKind::Symbol
                | TyKind::PrimitiveObject
                | TyKind::This
                | TyKind::GlobalThis
                | TyKind::BigIntLiteral(_)
                | TyKind::StringLiteral(_)
                | TyKind::NumberLiteral(_)
                | TyKind::TemplateLiteral(_)
                | TyKind::BooleanLiteral(_)
                | TyKind::Function(_)
                | TyKind::TypeReference(_)
                | TyKind::Array(_)
                | TyKind::Tuple(_)
                | TyKind::UniqueSymbol(_)
                | TyKind::Mapped(_)
                | TyKind::Object(_)
                | TyKind::ModuleNamespace(_)
                | TyKind::Infer(_)
                | TyKind::Conditional(_)
                | TyKind::IndexedAccess(_),
            ) => {
                // panic!("I don't know how to check assignability of\nsource: {source:?}\ntarget: {target:?}")
                false
            }
            (TyKind::None, _) => false,
        }
    }

    fn property_name_from_key_type(&self, ty: Ty<'a>) -> Option<&'a str> {
        match self.ty_kind(ty) {
            TyKind::StringLiteral(literal) => Some(literal.value),
            TyKind::NumberLiteral(literal) => literal.raw.as_ref().map(oxc_str::Str::as_str),
            TyKind::BooleanLiteral(true) => Some("true"),
            TyKind::BooleanLiteral(false) => Some("false"),
            _ => None,
        }
    }

    fn keyof_type_contains_property(&self, target: Ty<'a>, name: &str, depth: usize) -> bool {
        if depth >= ASSIGNABILITY_MAX_DEPTH {
            return false;
        }

        match self.ty_kind(target) {
            TyKind::Object(object) => object
                .properties
                .iter()
                .any(|property| !property.computed && property.name == name),
            TyKind::Intersection(intersection) => intersection
                .types
                .iter()
                .any(|ty| self.keyof_type_contains_property(*ty, name, depth + 1)),
            _ => false,
        }
    }

    fn type_arguments_assignable_to(
        &self,
        source_arguments: &[Ty<'a>],
        target_arguments: &[Ty<'a>],
        depth: usize,
    ) -> bool {
        source_arguments.len() == target_arguments.len()
            && source_arguments.iter().zip(target_arguments.iter()).all(
                |(source_argument, target_argument)| {
                    self.is_assignable_to_at_depth(*source_argument, *target_argument, depth)
                },
            )
    }

    fn properties_assignable_to(
        &self,
        source_properties: &[TyProperty<'a>],
        target_properties: &[TyProperty<'a>],
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
                && !self.is_assignable_to_at_depth(Ty::undefined(), target_property.ty, depth)
            {
                return false;
            }

            self.is_assignable_to_at_depth(source_property.ty, target_property.ty, depth)
        })
    }
}

#[cfg(test)]
mod tests {
    use oxc_allocator::Allocator;
    use std::path::{Path, PathBuf};

    use crate::{
        checker::Checker,
        program::{HostModuleResolution, ProgramHost, ProgramStore, ProgramStoreBuilder},
    };

    use super::*;

    struct TestProgramHost;

    impl ProgramHost for TestProgramHost {
        fn read_source(&self, _path: &Path) -> crate::program::ProgramStoreResult<String> {
            Ok(String::new())
        }

        fn canonicalize_path(&self, path: &Path) -> PathBuf {
            path.to_path_buf()
        }

        fn resolve_module(&self, _containing_file: &Path, specifier: &str) -> HostModuleResolution {
            HostModuleResolution::Missing(specifier.to_string())
        }
    }

    fn test_store<'a>(allocator: &'a Allocator) -> ProgramStore<'a> {
        ProgramStoreBuilder::new(allocator, TestProgramHost)
            .add_root_file("/test.ts")
            .without_default_lib()
            .build()
            .unwrap()
    }

    #[test]
    fn test_any_unknown_object_void_undefined_null_never_assignability() {
        let allocator = Allocator::default();
        let store = test_store(&allocator);
        let checker = Checker::new(&store);
        let is_assignable_to = |source, target| checker.is_assignable_to(source, target);

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
        let store = test_store(&allocator);
        let checker = Checker::new(&store);
        let arena = checker.arena;
        let is_assignable_to = |source, target| checker.is_assignable_to(source, target);

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
        let store = test_store(&allocator);
        let checker = Checker::new(&store);
        let arena = checker.arena;
        let is_assignable_to = |source, target| checker.is_assignable_to(source, target);

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
        let store = test_store(&allocator);
        let checker = Checker::new(&store);
        let arena = checker.arena;
        let is_assignable_to = |source, target| checker.is_assignable_to(source, target);

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
