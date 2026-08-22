use bitflags::bitflags;

use crate::types::{CheckerArena, Ty, TyKind};

bitflags! {
    /// Minimal facts about the possible runtime values of a type.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) struct TypeFacts: u8 {
        /// Nothing is known about the runtime values of this type, or it has no possible runtime values (e.g. `never`).
        const NONE = 0;
        /// The type has at least one possible runtime value that is truthy.
        const TRUTHY = 1 << 0;
        /// The type has at least one possible runtime value that is falsy.
        const FALSY = 1 << 1;
    }
}

pub(crate) fn get_type_facts<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> TypeFacts {
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
            facts | get_type_facts(arena, *ty)
        }),
        TyKind::Never => TypeFacts::NONE,
        _ => TypeFacts::TRUTHY | TypeFacts::FALSY,
    }
}
