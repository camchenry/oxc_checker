use std::{cell::RefCell, rc::Rc};

use oxc_allocator::Vec as ArenaVec;

use crate::types::{CheckerArena, Ty, TyTypeParameter, TypeData};

type TypeParameterResolver<'a> = Rc<RefCell<dyn FnMut(&str) -> Option<Ty<'a>> + 'a>>;

#[derive(Clone, Debug, Default)]
pub(crate) struct TypeParameterSubstitutions<'a> {
    pairs: Vec<(TyTypeParameter<'a>, Ty<'a>)>,
}

impl<'a> TypeParameterSubstitutions<'a> {
    pub(crate) fn new() -> Self {
        Self { pairs: Vec::new() }
    }

    pub(crate) fn insert(&mut self, type_parameter: TyTypeParameter<'a>, ty: Ty<'a>) {
        if let Some((_, existing)) = self
            .pairs
            .iter_mut()
            .find(|(existing, _)| *existing == type_parameter)
        {
            *existing = ty;
        } else {
            self.pairs.push((type_parameter, ty));
        }
    }

    pub(crate) fn get(&self, type_parameter: TyTypeParameter<'a>) -> Option<Ty<'a>> {
        self.pairs
            .iter()
            .find_map(|(existing, ty)| (*existing == type_parameter).then_some(*ty))
    }

    pub(crate) fn contains(&self, type_parameter: TyTypeParameter<'a>) -> bool {
        self.get(type_parameter).is_some()
    }

    pub(crate) fn to_mapper(&self, arena: CheckerArena<'a>) -> TypeMapper<'a> {
        TypeMapper::from_pairs(
            arena,
            self.pairs
                .iter()
                .map(|(type_parameter, ty)| {
                    (
                        Ty::type_reference(arena, type_parameter.name, std::iter::empty()),
                        *ty,
                    )
                })
                .collect(),
        )
    }
}

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
    ContextualInference {
        arena: CheckerArena<'a>,
        sources: ArenaVec<'a, Ty<'a>>,
        fallback_targets: ArenaVec<'a, Ty<'a>>,
        fixed: RefCell<Vec<bool>>,
        resolver: TypeParameterResolver<'a>,
    },
}

impl<'a> TypeMapper<'a> {
    pub(crate) fn single(source: Ty<'a>, target: Ty<'a>) -> Self {
        Self::Simple { source, target }
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

    pub(crate) fn from_contextual_inference_pairs(
        arena: CheckerArena<'a>,
        pairs: Vec<(Ty<'a>, Ty<'a>)>,
        resolver: impl FnMut(&str) -> Option<Ty<'a>> + 'a,
    ) -> Self {
        match pairs.len() {
            0 => Self::Empty,
            _ => {
                let len = pairs.len();
                Self::ContextualInference {
                    arena,
                    sources: arena.vec_from_iter(pairs.iter().map(|(source, _)| *source)),
                    fallback_targets: arena
                        .vec_from_iter(pairs.into_iter().map(|(_, target)| target)),
                    fixed: RefCell::new(vec![false; len]),
                    resolver: Rc::new(RefCell::new(resolver)),
                }
            }
        }
    }

    pub(crate) fn with_prepend_mapping(
        &self,
        arena: CheckerArena<'a>,
        source: Ty<'a>,
        target: Ty<'a>,
    ) -> Self {
        let mut pairs = vec![(source, target)];
        self.push_pairs_excluding(arena, &mut pairs, source);
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
        pairs.retain(|(source, _)| !is_bare_type_reference_with_name(arena, *source, &names));
        Self::from_pairs(arena, pairs)
    }

    pub(crate) fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub(crate) fn map(&self, arena: CheckerArena<'a>, ty: Ty<'a>) -> Ty<'a> {
        match self {
            Self::Empty => ty,
            Self::Simple { source, target } => {
                if arena.is_type_identical_to(ty, *source) {
                    *target
                } else {
                    ty
                }
            }
            Self::Array { sources, targets } => sources
                .iter()
                .zip(targets.iter())
                .find_map(|(source, target)| {
                    arena.is_type_identical_to(ty, *source).then_some(*target)
                })
                .unwrap_or(ty),
            Self::ContextualInference {
                arena: contextual_arena,
                sources,
                fallback_targets,
                fixed,
                resolver,
            } => sources
                .iter()
                .zip(fallback_targets.iter())
                .enumerate()
                .find_map(|(index, (source, fallback_target))| {
                    if !arena.is_type_identical_to(ty, *source) {
                        return None;
                    }
                    fixed.borrow_mut()[index] = true;
                    let resolved = match contextual_arena.type_data(*source) {
                        TypeData::TypeReference(reference)
                            if reference.type_arguments.is_empty() =>
                        {
                            resolver.borrow_mut()(reference.name)
                        }
                        _ => None,
                    };
                    Some(resolved.unwrap_or(*fallback_target))
                })
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
            Self::ContextualInference {
                sources,
                fallback_targets,
                ..
            } => {
                pairs.extend(
                    sources
                        .iter()
                        .copied()
                        .zip(fallback_targets.iter().copied()),
                );
            }
        }
    }

    fn push_pairs_excluding(
        &self,
        arena: CheckerArena<'a>,
        pairs: &mut Vec<(Ty<'a>, Ty<'a>)>,
        excluded: Ty<'a>,
    ) {
        match self {
            Self::Empty => {}
            Self::Simple { source, target } => {
                if !arena.is_type_identical_to(*source, excluded) {
                    pairs.push((*source, *target));
                }
            }
            Self::Array { sources, targets } => {
                pairs.extend(
                    sources
                        .iter()
                        .copied()
                        .zip(targets.iter().copied())
                        .filter(|(source, _)| !arena.is_type_identical_to(*source, excluded)),
                );
            }
            Self::ContextualInference {
                sources,
                fallback_targets,
                ..
            } => {
                pairs.extend(
                    sources
                        .iter()
                        .copied()
                        .zip(fallback_targets.iter().copied())
                        .filter(|(source, _)| !arena.is_type_identical_to(*source, excluded)),
                );
            }
        }
    }
}

fn is_bare_type_reference_with_name<'a>(
    arena: CheckerArena<'a>,
    ty: Ty<'a>,
    names: &[&'a str],
) -> bool {
    matches!(arena.type_data(ty), TypeData::TypeReference(reference) if reference.type_arguments.is_empty() && names.contains(&reference.name))
}

#[cfg(test)]
mod tests {
    use oxc_allocator::Allocator;

    use super::*;

    #[test]
    fn contextual_inference_mapper_resolves_type_parameter_when_read() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let source = Ty::type_reference(arena, "T", std::iter::empty());
        let resolved_names = Rc::new(RefCell::new(Vec::new()));
        let resolved_names_for_mapper = Rc::clone(&resolved_names);

        let mapper = TypeMapper::from_contextual_inference_pairs(
            arena,
            vec![(source, Ty::unknown())],
            move |name| {
                resolved_names_for_mapper
                    .borrow_mut()
                    .push(name.to_string());
                Some(Ty::string())
            },
        );

        assert_eq!(mapper.map(arena, source), Ty::string());
        assert_eq!(resolved_names.borrow().as_slice(), &["T".to_string()]);

        let TypeMapper::ContextualInference { fixed, .. } = &mapper else {
            panic!("expected contextual inference mapper");
        };
        assert_eq!(fixed.borrow().as_slice(), &[true]);
    }
}
