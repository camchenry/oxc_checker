use bitflags::bitflags;

use crate::types::{CheckerArena, Ty, TyKind, TypeBuilder};

bitflags! {
    /// Minimal facts about the possible runtime values of a type.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) struct TypeFacts: u8 {
        const NONE = 0;
        const TRUTHY = 1 << 0;
        const FALSY = 1 << 1;
    }
}

pub(crate) fn get_logical_not_type<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> Ty<'a> {
    let types = TypeBuilder::new(arena);
    match get_type_facts(arena, ty, TypeFacts::TRUTHY | TypeFacts::FALSY) {
        TypeFacts::TRUTHY => types.boolean_false(),
        TypeFacts::FALSY => types.boolean_true(),
        _ => types.boolean(),
    }
}

pub(crate) fn get_type_facts<'a>(
    arena: CheckerArena<'a>,
    ty: Ty<'a>,
    mask: TypeFacts,
) -> TypeFacts {
    get_type_facts_worker(arena, ty) & mask
}

fn get_type_facts_worker<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> TypeFacts {
    match arena.ty_kind(ty) {
        TyKind::String
        | TyKind::Number
        | TyKind::Boolean
        | TyKind::Bigint
        | TyKind::Any
        | TyKind::Error(_)
        | TyKind::Unknown => TypeFacts::TRUTHY | TypeFacts::FALSY,
        TyKind::StringLiteral(literal) => {
            if literal.value.is_empty() {
                TypeFacts::FALSY
            } else {
                TypeFacts::TRUTHY
            }
        }
        TyKind::NumberLiteral(literal) => {
            if literal.value == 0.0 {
                TypeFacts::FALSY
            } else {
                TypeFacts::TRUTHY
            }
        }
        TyKind::BooleanLiteral(value) => {
            if value {
                TypeFacts::TRUTHY
            } else {
                TypeFacts::FALSY
            }
        }
        TyKind::BigIntLiteral(literal) => {
            if literal.value == "0" {
                TypeFacts::FALSY
            } else {
                TypeFacts::TRUTHY
            }
        }
        TyKind::Undefined | TyKind::Null | TyKind::Void => TypeFacts::FALSY,
        TyKind::Symbol
        | TyKind::UniqueSymbol(_)
        | TyKind::PrimitiveObject
        | TyKind::ModuleNamespace(_)
        | TyKind::Function(_)
        | TyKind::Array(_)
        | TyKind::Tuple(_)
        | TyKind::GlobalThis
        | TyKind::TypeQuery(_) => TypeFacts::TRUTHY,
        TyKind::Object(object) if !object.is_empty() => TypeFacts::TRUTHY,
        TyKind::Union(union) => union.types.iter().fold(TypeFacts::NONE, |facts, ty| {
            facts | get_type_facts_worker(arena, *ty)
        }),
        TyKind::Never => TypeFacts::NONE,
        _ => TypeFacts::TRUTHY | TypeFacts::FALSY,
    }
}
