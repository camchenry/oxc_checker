use crate::{
    TupleElement, TyProperty,
    checker::Checker,
    limits::ASSIGNABILITY_MAX_DEPTH,
    mapper::TypeMapper,
    type_predicate_kinds_match,
    types::{Ty, TyKind, function_maximum_argument_count, function_minimum_argument_count},
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
                self.get_global_this_property_type(name).map(|source_type| {
                    if source_type == self.ty.global_this() {
                        source_type
                    } else {
                        self.global_symbols.global_this_value_symbol(name).map_or(
                            source_type,
                            |symbol| {
                                self.apparent_type_for_conditional_match(
                                    symbol.program_id,
                                    source_type,
                                    depth + 1,
                                )
                            },
                        )
                    }
                })
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
                    .is_some_and(|name| self.get_global_this_property_type(name).is_some()),
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

        let source_kind = self.ty_kind(source);
        let target_kind = self.ty_kind(target);

        match (source_kind, target_kind) {
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
            (TyKind::Union(source_union), _) => source_union.types.iter().all(|source_type| {
                self.is_assignable_to_at_depth(*source_type, target, next_depth)
            }),
            (_, TyKind::Union(target_union)) => target_union.types.iter().any(|target_type| {
                self.is_assignable_to_at_depth(source, *target_type, next_depth)
            }),
            (TyKind::TypeParameter(source), TyKind::TypeParameter(target)) => source == target,
            (TyKind::TypeParameter(source), _) => {
                source.constraint_type.is_some_and(|constraint| {
                    self.is_assignable_to_at_depth(constraint, target, next_depth)
                })
            }
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
            (TyKind::Intersection(intersection), TyKind::Object(_)) => intersection
                .types
                .iter()
                .all(|ty| self.is_assignable_to_at_depth(target, *ty, next_depth)),
            (TyKind::Intersection(intersection), TyKind::TypeParameter(_)) => intersection
                .types
                .iter()
                .any(|ty| self.is_assignable_to_at_depth(*ty, target, next_depth)),
            (TyKind::Intersection(intersection), other) if other.is_primitive() => {
                // Allow branded types to be assignable to their base type.
                intersection
                    .types
                    .iter()
                    .any(|ty| self.is_assignable_to_at_depth(*ty, target, next_depth))
            }
            (TyKind::Object(_), TyKind::Intersection(intersection)) => intersection
                .types
                .iter()
                .all(|ty| self.is_assignable_to_at_depth(source, *ty, next_depth)),
            (TyKind::Intersection(_), TyKind::Intersection(_))
                if self.arena().is_type_identical_to(source, target) =>
            {
                true
            }
            (TyKind::Function(source), TyKind::Function(target)) => {
                let source_mapper = if source.type_parameters.is_empty()
                    || target.type_parameters.is_empty()
                {
                    TypeMapper::Empty
                } else {
                    if source.type_parameters.len() != target.type_parameters.len() {
                        return false;
                    }
                    let mapper = TypeMapper::from_type_parameters_and_arguments(
                        self.arena(),
                        source.type_parameters.iter().copied(),
                        target
                            .type_parameters
                            .iter()
                            .map(|parameter| self.arena().type_parameter_type(*parameter)),
                    );
                    if !source
                        .type_parameters
                        .iter()
                        .zip(&target.type_parameters)
                        .all(|(source, target)| {
                            match (source.constraint_type, target.constraint_type) {
                                (Some(source), Some(target)) => self.arena().is_type_identical_to(
                                    self.instantiate_type(source, &mapper),
                                    target,
                                ),
                                (None, None) => true,
                                _ => false,
                            }
                        })
                    {
                        return false;
                    }
                    mapper
                };

                // If the number of required arguments for the source is greater than the
                // largest possible number of arguments for the target (that is: no overlap),
                // then the functions are not assignable.
                let source_minimum_argument_count =
                    function_minimum_argument_count(self.arena(), source);
                let target_maximum_argument_count =
                    function_maximum_argument_count(self.arena(), target);
                if target_maximum_argument_count
                    .is_some_and(|target_count| source_minimum_argument_count > target_count)
                {
                    return false;
                }

                // Each parameter must be assignable to the corresponding parameter in the target function
                let parameters_match = source.parameters.iter().zip(target.parameters.iter()).all(
                    |(source_parameter, target_parameter)| {
                        self.is_assignable_to_at_depth(
                            target_parameter.ty,
                            self.instantiate_type(source_parameter.ty, &source_mapper),
                            next_depth,
                        )
                    },
                );
                if !parameters_match {
                    return false;
                }

                // Functions that return a value can be assigned to a function that returns void,
                // because the caller ignores its result.
                let target_return_type = target.return_type();
                if self.ty_kind(target_return_type) == TyKind::Void {
                    return true;
                }

                // Type predicates (e.g., `x is string`) must match in their target types
                let type_predicate_matches = match (source.type_predicate, target.type_predicate) {
                    (Some(source_predicate), Some(target_predicate)) => {
                        type_predicate_kinds_match(source_predicate, target_predicate)
                            && match (
                                source_predicate.target_type(),
                                target_predicate.target_type(),
                            ) {
                                (Some(source_type), Some(target_type)) => self
                                    .is_assignable_to_at_depth(
                                        self.instantiate_type(source_type, &source_mapper),
                                        target_type,
                                        next_depth,
                                    ),
                                (None, None) => true,
                                _ => false,
                            }
                    }
                    (Some(type_predicate), None) => {
                        // If the source has a type predicate and the target does not, it's fine as long as: the target
                        // has a boolean return type, and the source type predicate is a type guard (e.g., `x is string`)
                        // In other words, `(x: string) => x is string` is assignable to `(x: string) => boolean`
                        self.ty_kind(target.return_type()) == TyKind::Boolean
                            && type_predicate.is_type_guard()
                    }
                    (None, Some(_)) => false,
                    (None, None) => true,
                };
                if !type_predicate_matches {
                    return false;
                }

                // Check that the return type matches
                let source_return_type =
                    self.instantiate_type(source.return_type(), &source_mapper);
                let return_type_matches = self.is_assignable_to_at_depth(
                    source_return_type,
                    target_return_type,
                    next_depth,
                );
                if !return_type_matches {
                    return false;
                }

                // Otherwise, assume the functions are assignable.
                true
            }
            (TyKind::TypeReference(source), TyKind::TypeReference(target)) => {
                source.has_identical_target(target)
                    && self.type_arguments_assignable_to(
                        &source.type_arguments,
                        &target.type_arguments,
                        next_depth,
                    )
            }
            (TyKind::Class(_) | TyKind::Function(_), TyKind::TypeReference(reference)) => {
                reference.target.is_some_and(|symbol| {
                    if self
                        .class_reference_has_private_instance_members(symbol.program_id, reference)
                    {
                        return false;
                    }
                    self.get_class_instance_type_for_reference(symbol.program_id, reference)
                        .is_some_and(|instance_type| {
                            let TyKind::Object(instance) = self.ty_kind(instance_type) else {
                                return false;
                            };
                            self.type_properties_assignable_to(
                                symbol.program_id,
                                source,
                                instance.properties,
                                next_depth,
                            )
                        })
                })
            }
            (TyKind::Class(source), TyKind::Class(target)) => self.is_assignable_to_at_depth(
                source.constructor_type,
                target.constructor_type,
                next_depth,
            ),
            (TyKind::Class(source), _) => {
                self.is_assignable_to_at_depth(source.constructor_type, target, next_depth)
            }
            (_, TyKind::Class(target)) => {
                self.is_assignable_to_at_depth(source, target.constructor_type, next_depth)
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
                // Assignment of an immutable array to a mutable array is not allowed
                if source.readonly && !target.readonly {
                    return false;
                }
                self.is_assignable_to_at_depth(source.element_type, target.element_type, next_depth)
            }
            (TyKind::Tuple(source), TyKind::Array(target)) => {
                // Assignment of an immutable array to a mutable array is not allowed
                if source.readonly && !target.readonly {
                    return false;
                }
                source.elements.iter().all(|element| {
                    self.is_assignable_to_at_depth(element.ty(), target.element_type, next_depth)
                })
            }
            (TyKind::Tuple(source), TyKind::Tuple(target)) => {
                // Assignment of an immutable array to a mutable array is not allowed
                if source.readonly && !target.readonly {
                    return false;
                }
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
            (TyKind::TemplateLiteral(_), TyKind::String) => true,
            (TyKind::BigIntLiteral(_), TyKind::Bigint) => true,
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
                | TyKind::TypeParameter(_)
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
            TyKind::TypeReference(reference) => self
                .expand_type_alias_for_relation(target, depth + 1)
                .or_else(|| {
                    reference.target.map(|symbol| {
                        self.apparent_type_for_conditional_match(
                            symbol.program_id,
                            target,
                            depth + 1,
                        )
                    })
                })
                .is_some_and(|expanded| {
                    expanded != target
                        && self.keyof_type_contains_property(expanded, name, depth + 1)
                }),
            TyKind::IndexedAccess(indexed_access) => self
                .property_name_from_key_type(indexed_access.index_type)
                .and_then(|property_name| {
                    self.property_type_for_relation(
                        indexed_access.object_type,
                        property_name,
                        depth + 1,
                    )
                })
                .is_some_and(|property_type| {
                    self.keyof_type_contains_property(property_type, name, depth + 1)
                }),
            TyKind::Intersection(intersection) => intersection
                .types
                .iter()
                .any(|ty| self.keyof_type_contains_property(*ty, name, depth + 1)),
            _ => false,
        }
    }

    fn property_type_for_relation(
        &self,
        target: Ty<'a>,
        name: &str,
        depth: usize,
    ) -> Option<Ty<'a>> {
        if depth >= ASSIGNABILITY_MAX_DEPTH {
            return None;
        }

        match self.ty_kind(target) {
            TyKind::Object(object) => object
                .properties
                .iter()
                .find(|property| !property.computed && property.name == name)
                .map(|property| property.ty),
            TyKind::TypeReference(reference) => self
                .expand_type_alias_for_relation(target, depth + 1)
                .or_else(|| {
                    reference.target.map(|symbol| {
                        self.apparent_type_for_conditional_match(
                            symbol.program_id,
                            target,
                            depth + 1,
                        )
                    })
                })
                .filter(|expanded| *expanded != target)
                .and_then(|expanded| self.property_type_for_relation(expanded, name, depth + 1)),
            TyKind::Intersection(intersection) => intersection
                .types
                .iter()
                .find_map(|ty| self.property_type_for_relation(*ty, name, depth + 1)),
            _ => None,
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

    fn type_properties_assignable_to(
        &self,
        program_id: crate::program::ProgramId,
        source: Ty<'a>,
        target_properties: &[TyProperty<'a>],
        depth: usize,
    ) -> bool {
        target_properties.iter().all(|target_property| {
            let source_type = self
                .property_type_for_relation(source, target_property.name, depth)
                .or_else(|| {
                    self.get_property_type_of_global_interface_type(
                        program_id,
                        source,
                        target_property.name,
                    )
                });
            source_type.map_or(target_property.optional, |source_type| {
                self.is_assignable_to_at_depth(source_type, target_property.ty, depth)
            })
        })
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
                && !self.is_assignable_to_at_depth(Ty::Undefined, target_property.ty, depth)
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
    use std::{
        borrow::Cow,
        path::{Path, PathBuf},
    };

    use crate::{
        TyTypePredicate, TypeBuilder,
        checker::Checker,
        program::{HostModuleResolution, ProgramHost, ProgramStore, ProgramStoreBuilder},
        type_predicate_return_type,
    };

    use super::*;

    struct TestProgramHost;

    impl ProgramHost for TestProgramHost {
        fn read_source(&self, _path: &Path) -> crate::program::ProgramStoreResult<Cow<'_, str>> {
            Ok(Cow::Borrowed(""))
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
        assert!(is_assignable_to(Ty::Any, Ty::Any));
        assert!(is_assignable_to(Ty::Unknown, Ty::Unknown));
        assert!(is_assignable_to(Ty::PrimitiveObject, Ty::PrimitiveObject));
        assert!(is_assignable_to(Ty::Void, Ty::Void));
        assert!(is_assignable_to(Ty::Undefined, Ty::Undefined));
        assert!(is_assignable_to(Ty::Null, Ty::Null));
        assert!(is_assignable_to(Ty::Never, Ty::Never));
        // `any` is assignable to all types, except for `never`
        assert!(is_assignable_to(Ty::Any, Ty::Unknown));
        assert!(is_assignable_to(Ty::Any, Ty::PrimitiveObject));
        assert!(is_assignable_to(Ty::Any, Ty::Void));
        assert!(is_assignable_to(Ty::Any, Ty::Undefined));
        assert!(is_assignable_to(Ty::Any, Ty::Null));
        assert!(!is_assignable_to(Ty::Any, Ty::Never));
        // `unknown` is basically the same as `any`, but doesn't allow for any type to be assigned to it
        assert!(is_assignable_to(Ty::Unknown, Ty::Any));
        assert!(!is_assignable_to(Ty::Unknown, Ty::PrimitiveObject));
        assert!(!is_assignable_to(Ty::Unknown, Ty::Void));
        assert!(!is_assignable_to(Ty::Unknown, Ty::Undefined));
        assert!(!is_assignable_to(Ty::Unknown, Ty::Null));
        assert!(!is_assignable_to(Ty::Unknown, Ty::Never));
        // `object` is assignable to `any`, `unknown`, and itself, but not to `void`, `undefined`, `null`, or `never`
        assert!(is_assignable_to(Ty::PrimitiveObject, Ty::Any));
        assert!(is_assignable_to(Ty::PrimitiveObject, Ty::Unknown));
        assert!(!is_assignable_to(Ty::PrimitiveObject, Ty::Void));
        assert!(!is_assignable_to(Ty::PrimitiveObject, Ty::Undefined));
        assert!(!is_assignable_to(Ty::PrimitiveObject, Ty::Null));
        assert!(!is_assignable_to(Ty::PrimitiveObject, Ty::Never));
        // `void` is not assignable to anything, except for `any` and `unknown`
        assert!(is_assignable_to(Ty::Void, Ty::Any));
        assert!(is_assignable_to(Ty::Void, Ty::Unknown));
        assert!(!is_assignable_to(Ty::Void, Ty::PrimitiveObject));
        assert!(!is_assignable_to(Ty::Void, Ty::Undefined));
        assert!(!is_assignable_to(Ty::Void, Ty::Null));
        assert!(!is_assignable_to(Ty::Void, Ty::Never));
        // `undefined` is not assignable to anything, except for `any`, `unknown`, and `void`
        assert!(is_assignable_to(Ty::Undefined, Ty::Any));
        assert!(is_assignable_to(Ty::Undefined, Ty::Unknown));
        assert!(is_assignable_to(Ty::Undefined, Ty::Void));
        assert!(!is_assignable_to(Ty::Undefined, Ty::PrimitiveObject));
        assert!(!is_assignable_to(Ty::Undefined, Ty::Null));
        assert!(!is_assignable_to(Ty::Undefined, Ty::Never));
        // `null` is not assignable to anything, except for `any` and `unknown`
        assert!(is_assignable_to(Ty::Null, Ty::Any));
        assert!(is_assignable_to(Ty::Null, Ty::Unknown));
        assert!(!is_assignable_to(Ty::Null, Ty::PrimitiveObject));
        assert!(!is_assignable_to(Ty::Null, Ty::Void));
        assert!(!is_assignable_to(Ty::Null, Ty::Undefined));
        assert!(!is_assignable_to(Ty::Null, Ty::Never));
        // `never` is assignable to everything
        assert!(is_assignable_to(Ty::Never, Ty::Any));
        assert!(is_assignable_to(Ty::Never, Ty::Unknown));
        assert!(is_assignable_to(Ty::Never, Ty::PrimitiveObject));
        assert!(is_assignable_to(Ty::Never, Ty::Void));
        assert!(is_assignable_to(Ty::Never, Ty::Undefined));
        assert!(is_assignable_to(Ty::Never, Ty::Null));
    }

    #[test]
    fn test_intersection_assignability() {
        let allocator = Allocator::default();
        let store = test_store(&allocator);
        let checker = Checker::new(&store);
        let arena = checker.arena;
        let is_assignable_to = |source, target| checker.is_assignable_to(source, target);

        let number_and_string = arena.intersection([
            arena.object([TypeBuilder::new(arena).property("a", Ty::Number)]),
            arena.object([TypeBuilder::new(arena).property("b", Ty::String)]),
        ]);

        // { a: number, b: string } -> { a: number } & { b: string }
        assert!(is_assignable_to(
            arena.object([
                TypeBuilder::new(arena).property("a", Ty::Number),
                TypeBuilder::new(arena).property("b", Ty::String)
            ]),
            number_and_string
        ));
        // { a: number } -!> { a: number, b: string }
        assert!(!is_assignable_to(
            arena.object([TypeBuilder::new(arena).property("a", Ty::Number)]),
            arena.object([
                TypeBuilder::new(arena).property("a", Ty::Number),
                TypeBuilder::new(arena).property("b", Ty::String)
            ]),
        ));
        // { a: number } & { b: string } -> { a: number, b: string }
        assert!(is_assignable_to(
            number_and_string,
            arena.object([
                TypeBuilder::new(arena).property("a", Ty::Number),
                TypeBuilder::new(arena).property("b", Ty::String)
            ]),
        ));

        // Branded types
        let string_brand = arena.intersection([
            Ty::String,
            arena.object([
                TypeBuilder::new(arena).property("__brand", arena.string_literal("brand"))
            ]),
        ]);
        // `string & { __brand: "brand" }` is assignable to `string`
        assert!(is_assignable_to(string_brand, Ty::String));

        let identical_string_brand = arena.intersection([
            Ty::String,
            arena.object([
                TypeBuilder::new(arena).property("__brand", arena.string_literal("brand"))
            ]),
        ]);
        assert_ne!(string_brand, identical_string_brand);
        assert!(arena.is_type_identical_to(string_brand, identical_string_brand));
        assert!(is_assignable_to(string_brand, identical_string_brand));
        assert!(is_assignable_to(identical_string_brand, string_brand));
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
            arena.object([
                TypeBuilder::new(arena).property("a", Ty::Number),
                TypeBuilder::new(arena).property("b", Ty::String)
            ]),
            arena.object([TypeBuilder::new(arena).property("a", Ty::Number)])
        ));

        // { a: number } is not assignable to { a: number, b: string }
        assert!(!is_assignable_to(
            arena.object([TypeBuilder::new(arena).property("a", Ty::Number)]),
            arena.object([
                TypeBuilder::new(arena).property("a", Ty::Number),
                TypeBuilder::new(arena).property("b", Ty::String)
            ]),
        ));

        // { a: number, b: string } is assignable to {}
        assert!(is_assignable_to(
            arena.object([
                TypeBuilder::new(arena).property("a", Ty::Number),
                TypeBuilder::new(arena).property("b", Ty::String)
            ]),
            arena.object([])
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
        assert!(is_assignable_to(Ty::PrimitiveObject, Ty::PrimitiveObject));
        // `object` is assignable to {}
        assert!(is_assignable_to(Ty::PrimitiveObject, arena.object([])));
        // `{}` is assignable to `object`
        assert!(is_assignable_to(arena.object([]), Ty::PrimitiveObject));
        // `{}` is not assignable to undefined, null
        assert!(!is_assignable_to(arena.object([]), Ty::Undefined));
        assert!(!is_assignable_to(arena.object([]), Ty::Null));
    }

    #[test]
    fn test_function_type_assignability() {
        let allocator = Allocator::default();
        let store = test_store(&allocator);
        let checker = Checker::new(&store);
        let arena = checker.arena;
        let ty = TypeBuilder::new(arena);
        let is_assignable_to = |source, target| checker.is_assignable_to(source, target);

        // (a: number) => void is assignable to (a: number) => void
        assert!(is_assignable_to(
            ty.function([], [ty.parameter("a", Ty::Number)], Ty::Void),
            ty.function([], [ty.parameter("a", Ty::Number)], Ty::Void)
        ));

        // Optional and rest parameters do not increase a source function's minimum arity.
        assert!(is_assignable_to(
            ty.function(
                [],
                [
                    ty.parameter("a", Ty::Number),
                    ty.parameter("b", Ty::Number).optional(true)
                ],
                Ty::Void
            ),
            ty.function([], [ty.parameter("a", Ty::Number)], Ty::Void)
        ));
        assert!(is_assignable_to(
            ty.function(
                [],
                [
                    ty.parameter("a", Ty::Number),
                    ty.parameter("rest", arena.array(Ty::Number)).rest(true)
                ],
                Ty::Void
            ),
            ty.function([], [ty.parameter("a", Ty::Number)], Ty::Void)
        ));

        let required_pair = arena.tuple(vec![
            TupleElement::Regular(Ty::Number),
            TupleElement::Regular(Ty::Number),
        ]);
        assert!(!is_assignable_to(
            ty.function(
                [],
                [ty.parameter("args", required_pair).rest(true)],
                Ty::Void
            ),
            ty.function([], [ty.parameter("arg", required_pair)], Ty::Void)
        ));

        // A target rest parameter can accept any number of source parameters.
        let number_array = arena.array(Ty::Number);
        assert!(is_assignable_to(
            ty.function(
                [],
                [
                    ty.parameter("a", number_array),
                    ty.parameter("b", number_array)
                ],
                Ty::Void
            ),
            ty.function(
                [],
                [ty.parameter("rest", number_array).rest(true)],
                Ty::Void
            )
        ));

        // '(value: string) => void' is not assignable to type '(value: string) => string'
        assert!(!is_assignable_to(
            ty.function([], [ty.parameter("value", Ty::String)], Ty::Void),
            ty.function([], [ty.parameter("value", Ty::String)], Ty::String)
        ));

        // '(value: string) => string' is assignable to type '(value: string) => void'
        assert!(is_assignable_to(
            ty.function([], [ty.parameter("value", Ty::String)], Ty::String),
            ty.function([], [ty.parameter("value", Ty::String)], Ty::Void)
        ));

        // Type predicate: `(value: string) => value is string` is assignable to `(value: string) => boolean`
        assert!(is_assignable_to(
            ty.function_with_type_predicate_and_display(
                [],
                [ty.parameter("value", Ty::String)],
                Ty::Boolean,
                Some(TyTypePredicate::Identifier {
                    parameter_name: "value",
                    parameter_index: Some(0),
                    target_type: Ty::String
                }),
                true,
            ),
            ty.function([], [ty.parameter("value", Ty::String)], Ty::Boolean)
        ));

        // Type assertion: `(value: string) => never` is assignable to `(value: string) => asserts value is string`
        assert!(is_assignable_to(
            ty.function([], [ty.parameter("value", Ty::String)], Ty::Never),
            ty.function_with_type_predicate_and_display(
                [],
                [ty.parameter("value", Ty::String)],
                type_predicate_return_type(true),
                Some(TyTypePredicate::AssertsIdentifier {
                    parameter_name: "value",
                    parameter_index: Some(0),
                    target_type: Some(Ty::String)
                }),
                true,
            )
        ));

        // Type assertion: `() => void` is assignable to `(x: unknown) => asserts x is string`
        assert!(is_assignable_to(
            ty.function([], [], Ty::Void),
            ty.function_with_type_predicate_and_display(
                [],
                [ty.parameter("x", Ty::Unknown)],
                type_predicate_return_type(true),
                Some(TyTypePredicate::AssertsIdentifier {
                    parameter_name: "x",
                    parameter_index: Some(0),
                    target_type: Some(Ty::String)
                }),
                true,
            )
        ));

        // `(x: unknown) => x is string` is assignable to `(x: unknown) => asserts x is string`
        assert!(is_assignable_to(
            ty.function_with_type_predicate_and_display(
                [],
                [ty.parameter("x", Ty::Unknown)],
                type_predicate_return_type(false),
                Some(TyTypePredicate::Identifier {
                    parameter_name: "x",
                    parameter_index: Some(0),
                    target_type: Ty::String
                }),
                true,
            ),
            ty.function_with_type_predicate_and_display(
                [],
                [ty.parameter("x", Ty::Unknown)],
                type_predicate_return_type(true),
                Some(TyTypePredicate::AssertsIdentifier {
                    parameter_name: "x",
                    parameter_index: Some(0),
                    target_type: Some(Ty::String)
                }),
                true,
            )
        ));
    }

    #[test]
    fn test_array_and_tuple_type_assignability() {
        let allocator = Allocator::default();
        let store = test_store(&allocator);
        let checker = Checker::new(&store);
        let arena = checker.arena;
        let ty = TypeBuilder::new(arena);
        let is_assignable_to = |source, target| checker.is_assignable_to(source, target);

        // number[] is not assignable to [number, number]
        assert!(!is_assignable_to(
            ty.array(Ty::Number),
            ty.tuple(vec![
                TupleElement::Regular(Ty::Number),
                TupleElement::Regular(Ty::Number)
            ])
        ));

        // [number, number] is assignable to number[]
        assert!(is_assignable_to(
            ty.tuple(vec![
                TupleElement::Regular(Ty::Number),
                TupleElement::Regular(Ty::Number)
            ]),
            ty.array(Ty::Number)
        ));

        // readonly number[] is not assignable to number[]
        assert!(!is_assignable_to(
            ty.generic_array(Ty::Number, true),
            ty.array(Ty::Number)
        ));

        // readonly [number, number] is not assignable to [number, number]
        assert!(!is_assignable_to(
            ty.readonly_tuple(vec![
                TupleElement::Regular(Ty::Number),
                TupleElement::Regular(Ty::Number)
            ]),
            ty.tuple(vec![
                TupleElement::Regular(Ty::Number),
                TupleElement::Regular(Ty::Number)
            ])
        ));

        // readonly [number, number] is not assignable to number[]
        assert!(!is_assignable_to(
            ty.readonly_tuple(vec![
                TupleElement::Regular(Ty::Number),
                TupleElement::Regular(Ty::Number)
            ]),
            ty.array(Ty::Number)
        ));
    }
}
