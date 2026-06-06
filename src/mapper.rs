use std::collections::HashMap;

use oxc_allocator::Vec as ArenaVec;

use crate::types::{CheckerArena, Ty, TyTypeParameter};

pub(crate) enum TypeMapper<'a> {
    Empty,
    Simple {
        source: Ty<'a>,
        target: Ty<'a>,
    },
    Array {
        sources: ArenaVec<'a, Ty<'a>>,
        targets: ArenaVec<'a, Ty<'a>>,
    },
}

impl<'a> TypeMapper<'a> {
    pub(crate) fn from_substitutions(
        arena: CheckerArena<'a>,
        substitutions: &HashMap<&'a str, Ty<'a>>,
    ) -> Self {
        match substitutions.len() {
            0 => Self::Empty,
            1 => {
                let (name, target) = substitutions.iter().next().expect("checked length");
                Self::Simple {
                    source: Ty::type_reference(arena, name, std::iter::empty()),
                    target: *target,
                }
            }
            _ => Self::Array {
                sources: arena.vec_from_iter(
                    substitutions
                        .keys()
                        .map(|name| Ty::type_reference(arena, name, std::iter::empty())),
                ),
                targets: arena.vec_from_iter(substitutions.values().copied()),
            },
        }
    }

    pub(crate) fn from_type_parameters_and_arguments(
        arena: CheckerArena<'a>,
        type_parameters: impl IntoIterator<Item = TyTypeParameter<'a>>,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Self {
        let pairs = type_parameters
            .into_iter()
            .zip(type_arguments)
            .map(|(type_parameter, type_argument)| {
                (
                    Ty::type_reference(arena, type_parameter.name, std::iter::empty()),
                    type_argument,
                )
            })
            .collect::<Vec<_>>();
        Self::from_pairs(arena, pairs)
    }

    pub(crate) fn with_prepend_mapping(
        &self,
        arena: CheckerArena<'a>,
        source: Ty<'a>,
        target: Ty<'a>,
    ) -> Self {
        let mut pairs = vec![(source, target)];
        self.push_pairs_excluding(&mut pairs, source);
        Self::from_pairs(arena, pairs)
    }

    pub(crate) fn without_type_parameter_names(
        &self,
        arena: CheckerArena<'a>,
        names: impl IntoIterator<Item = &'a str>,
    ) -> Self {
        let names = names.into_iter().collect::<Vec<_>>();
        let mut pairs = Vec::new();
        self.push_pairs(&mut pairs);
        pairs.retain(|(source, _)| !is_bare_type_reference_with_name(*source, &names));
        Self::from_pairs(arena, pairs)
    }

    pub(crate) fn has_non_identity_mapping_outside_names(
        &self,
        names: impl IntoIterator<Item = &'a str>,
    ) -> bool {
        let names = names.into_iter().collect::<Vec<_>>();
        let mut pairs = Vec::new();
        self.push_pairs(&mut pairs);
        pairs.into_iter().any(|(source, target)| {
            !is_bare_type_reference_with_name(source, &names) && source != target
        })
    }

    pub(crate) fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub(crate) fn map(&self, ty: Ty<'a>) -> Ty<'a> {
        match self {
            Self::Empty => ty,
            Self::Simple { source, target } => {
                if ty == *source {
                    *target
                } else {
                    ty
                }
            }
            Self::Array { sources, targets } => sources
                .iter()
                .zip(targets.iter())
                .find_map(|(source, target)| (ty == *source).then_some(*target))
                .unwrap_or(ty),
        }
    }

    fn from_pairs(arena: CheckerArena<'a>, pairs: Vec<(Ty<'a>, Ty<'a>)>) -> Self {
        match pairs.len() {
            0 => Self::Empty,
            1 => {
                let (source, target) = pairs.into_iter().next().expect("checked length");
                Self::Simple { source, target }
            }
            _ => Self::Array {
                sources: arena.vec_from_iter(pairs.iter().map(|(source, _)| *source)),
                targets: arena.vec_from_iter(pairs.into_iter().map(|(_, target)| target)),
            },
        }
    }

    fn push_pairs(&self, pairs: &mut Vec<(Ty<'a>, Ty<'a>)>) {
        match self {
            Self::Empty => {}
            Self::Simple { source, target } => pairs.push((*source, *target)),
            Self::Array { sources, targets } => {
                pairs.extend(sources.iter().copied().zip(targets.iter().copied()));
            }
        }
    }

    fn push_pairs_excluding(&self, pairs: &mut Vec<(Ty<'a>, Ty<'a>)>, excluded: Ty<'a>) {
        match self {
            Self::Empty => {}
            Self::Simple { source, target } => {
                if *source != excluded {
                    pairs.push((*source, *target));
                }
            }
            Self::Array { sources, targets } => {
                pairs.extend(
                    sources
                        .iter()
                        .copied()
                        .zip(targets.iter().copied())
                        .filter(|(source, _)| *source != excluded),
                );
            }
        }
    }
}

fn is_bare_type_reference_with_name<'a>(ty: Ty<'a>, names: &[&'a str]) -> bool {
    matches!(ty, Ty::TypeReference(reference) if reference.type_arguments.is_empty() && names.contains(&reference.name))
}
