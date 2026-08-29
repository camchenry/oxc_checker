use std::{cell::RefCell, rc::Rc};

use oxc_allocator::Vec as ArenaVec;
use smallvec::{SmallVec, smallvec};

use crate::types::{CheckerArena, Ty, TyKind, TyTypeParameter, TypeId};

type TypeParameterResolver<'a> = Rc<RefCell<dyn FnMut(&str) -> Option<Ty<'a>> + 'a>>;
type MapperPairs<'a> = SmallVec<[(Ty<'a>, Ty<'a>); 4]>;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum MapperCacheSource<'a> {
    TypeParameter(&'a str),
    Type(TypeId),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct MapperCacheEntry<'a> {
    source: MapperCacheSource<'a>,
    target: TypeId,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct TypeParameterSubstitutions<'a> {
    pairs: SmallVec<[(TyTypeParameter<'a>, Ty<'a>); 4]>,
}

impl<'a> TypeParameterSubstitutions<'a> {
    pub(crate) fn new() -> Self {
        Self {
            pairs: SmallVec::new(),
        }
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
                .map(|(type_parameter, ty)| (arena.type_parameter_type(*type_parameter), *ty))
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
                (arena.type_parameter_type(type_parameter), type_argument)
            })
            .collect::<MapperPairs<'a>>();
        Self::from_pairs(arena, pairs)
    }

    pub(crate) fn from_contextual_inference_pairs(
        arena: CheckerArena<'a>,
        pairs: Vec<(Ty<'a>, Ty<'a>)>,
        resolver: impl FnMut(&str) -> Option<Ty<'a>> + 'a,
    ) -> Self {
        if pairs.is_empty() {
            Self::Empty
        } else {
            let len = pairs.len();
            Self::ContextualInference {
                arena,
                sources: arena.vec_from_iter(pairs.iter().map(|(source, _)| *source)),
                fallback_targets: arena.vec_from_iter(pairs.into_iter().map(|(_, target)| target)),
                fixed: RefCell::new(vec![false; len]),
                resolver: Rc::new(RefCell::new(resolver)),
            }
        }
    }

    pub(crate) fn with_prepend_mapping(
        &self,
        arena: CheckerArena<'a>,
        source: Ty<'a>,
        target: Ty<'a>,
    ) -> Self {
        let mut pairs = smallvec![(source, target)];
        self.push_pairs_excluding(arena, &mut pairs, source);
        Self::from_pairs(arena, pairs)
    }

    pub(crate) fn without_type_parameter_names(
        &self,
        arena: CheckerArena<'a>,
        names: impl IntoIterator<Item = &'a str>,
    ) -> Self {
        let names = names.into_iter().collect::<Vec<_>>();
        let mut pairs = SmallVec::new();
        self.push_pairs(&mut pairs);
        pairs.retain(|(source, _)| !is_bare_type_reference_with_name(arena, *source, &names));
        Self::from_pairs(arena, pairs)
    }

    pub(crate) fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub(crate) fn has_concrete_type_parameter_mapping(&self, arena: CheckerArena<'a>) -> bool {
        let is_concrete = |source: Ty<'a>, target: Ty<'a>| {
            let Some(source_name) = type_parameter_name(arena, source) else {
                return false;
            };
            type_parameter_name(arena, target) != Some(source_name)
        };
        match self {
            Self::Empty => false,
            Self::Simple { source, target } => is_concrete(*source, *target),
            Self::Array { sources, targets } => sources
                .iter()
                .zip(targets.iter())
                .any(|(source, target)| is_concrete(*source, *target)),
            Self::ContextualInference { .. } => false,
        }
    }

    pub(crate) fn cache_entries(
        &self,
        arena: CheckerArena<'a>,
    ) -> Option<SmallVec<[MapperCacheEntry<'a>; 1]>> {
        let source_key = |source: Ty<'a>| match arena.ty_kind(source) {
            TyKind::TypeReference(reference)
                if reference.is_bare() && reference.target.is_none() =>
            {
                MapperCacheSource::TypeParameter(reference.name)
            }
            _ => MapperCacheSource::Type(source.id()),
        };
        match self {
            Self::Empty => Some(SmallVec::new()),
            Self::Simple { source, target } => Some(smallvec![MapperCacheEntry {
                source: source_key(*source),
                target: target.id(),
            }]),
            Self::Array { sources, targets } => Some(
                sources
                    .iter()
                    .zip(targets.iter())
                    .map(|(source, target)| MapperCacheEntry {
                        source: source_key(*source),
                        target: target.id(),
                    })
                    .collect(),
            ),
            Self::ContextualInference { .. } => None,
        }
    }

    pub(crate) fn map(&self, arena: CheckerArena<'a>, ty: Ty<'a>) -> Ty<'a> {
        match self {
            Self::Empty => ty,
            Self::Simple { source, target } => {
                if types_match_for_mapping(arena, ty, *source) {
                    *target
                } else {
                    ty
                }
            }
            Self::Array { sources, targets } => sources
                .iter()
                .zip(targets.iter())
                .find_map(|(source, target)| {
                    types_match_for_mapping(arena, ty, *source).then_some(*target)
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
                    if !types_match_for_mapping(arena, ty, *source) {
                        return None;
                    }
                    fixed.borrow_mut()[index] = true;
                    let resolved = match contextual_arena.ty_kind(*source) {
                        TyKind::TypeParameter(type_parameter) => {
                            resolver.borrow_mut()(type_parameter.name)
                        }
                        TyKind::TypeReference(reference) if reference.is_bare() => {
                            resolver.borrow_mut()(reference.name)
                        }
                        _ => None,
                    };
                    Some(resolved.unwrap_or(*fallback_target))
                })
                .unwrap_or(ty),
        }
    }

    fn from_pairs(arena: CheckerArena<'a>, pairs: MapperPairs<'a>) -> Self {
        match pairs.as_slice() {
            [] => Self::Empty,
            &[(source, target)] => Self::Simple { source, target },
            _ => Self::Array {
                sources: arena.vec_from_iter(pairs.iter().map(|(source, _)| *source)),
                targets: arena.vec_from_iter(pairs.into_iter().map(|(_, target)| target)),
            },
        }
    }

    fn push_pairs(&self, pairs: &mut MapperPairs<'a>) {
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
        pairs: &mut MapperPairs<'a>,
        excluded: Ty<'a>,
    ) {
        match self {
            Self::Empty => {}
            Self::Simple { source, target } => {
                if !types_match_for_mapping(arena, *source, excluded) {
                    pairs.push((*source, *target));
                }
            }
            Self::Array { sources, targets } => {
                pairs.extend(
                    sources
                        .iter()
                        .copied()
                        .zip(targets.iter().copied())
                        .filter(|(source, _)| !types_match_for_mapping(arena, *source, excluded)),
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
                        .filter(|(source, _)| !types_match_for_mapping(arena, *source, excluded)),
                );
            }
        }
    }
}

fn types_match_for_mapping<'a>(arena: CheckerArena<'a>, left: Ty<'a>, right: Ty<'a>) -> bool {
    if arena.is_type_identical_to(left, right) {
        return true;
    }
    match (arena.ty_kind(left), arena.ty_kind(right)) {
        (TyKind::TypeParameter(parameter), TyKind::TypeReference(reference))
        | (TyKind::TypeReference(reference), TyKind::TypeParameter(parameter)) => {
            reference.is_bare() && parameter.name == reference.name
        }
        _ => false,
    }
}

fn type_parameter_name<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> Option<&'a str> {
    match arena.ty_kind(ty) {
        TyKind::TypeParameter(type_parameter) => Some(type_parameter.name),
        TyKind::TypeReference(reference) if reference.is_bare() => Some(reference.name),
        _ => None,
    }
}

fn is_bare_type_reference_with_name<'a>(
    arena: CheckerArena<'a>,
    ty: Ty<'a>,
    names: &[&'a str],
) -> bool {
    match arena.ty_kind(ty) {
        TyKind::TypeParameter(type_parameter) => names.contains(&type_parameter.name),
        TyKind::TypeReference(reference) => reference.is_bare() && names.contains(&reference.name),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use oxc_allocator::Allocator;

    use super::*;
    use crate::types::TypeBuilder;

    #[test]
    fn mapper_preserves_same_named_type_parameter_identity() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let types = TypeBuilder::new(arena);
        let source = arena.type_parameter_type(types.type_parameter("T", Some(Ty::string()), None));
        let distinct =
            arena.type_parameter_type(types.type_parameter("T", Some(Ty::number()), None));
        let mapper = TypeMapper::single(source, Ty::boolean());

        assert_eq!(mapper.map(arena, source), Ty::boolean());
        assert_eq!(mapper.map(arena, distinct), distinct);
    }

    #[test]
    fn contextual_inference_mapper_resolves_type_parameter_when_read() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);
        let source = arena.type_reference("T", std::iter::empty());
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
