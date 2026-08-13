use bitflags::bitflags;

use crate::types::{CheckerArena, Ty, TypeData};

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
    match get_type_facts(arena, ty, TypeFacts::TRUTHY | TypeFacts::FALSY) {
        TypeFacts::TRUTHY => Ty::boolean_false(),
        TypeFacts::FALSY => Ty::boolean_true(),
        _ => Ty::boolean(),
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
    match arena.type_data(ty) {
        TypeData::String
        | TypeData::Number
        | TypeData::Boolean
        | TypeData::Bigint
        | TypeData::Any
        | TypeData::Error(_)
        | TypeData::Unknown => TypeFacts::TRUTHY | TypeFacts::FALSY,
        TypeData::StringLiteral(literal) => {
            if literal.value.is_empty() {
                TypeFacts::FALSY
            } else {
                TypeFacts::TRUTHY
            }
        }
        TypeData::NumberLiteral(literal) => {
            if literal.value == 0.0 {
                TypeFacts::FALSY
            } else {
                TypeFacts::TRUTHY
            }
        }
        TypeData::BooleanLiteral(value) => {
            if value {
                TypeFacts::TRUTHY
            } else {
                TypeFacts::FALSY
            }
        }
        TypeData::BigIntLiteral(literal) => {
            if bigint_literal_value_is_zero(literal.value) {
                TypeFacts::FALSY
            } else {
                TypeFacts::TRUTHY
            }
        }
        TypeData::Undefined | TypeData::Null | TypeData::Void => TypeFacts::FALSY,
        TypeData::Symbol
        | TypeData::UniqueSymbol(_)
        | TypeData::PrimitiveObject
        | TypeData::ModuleNamespace(_)
        | TypeData::Function(_)
        | TypeData::Array(_)
        | TypeData::Tuple(_)
        | TypeData::GlobalThis
        | TypeData::TypeQuery(_) => TypeFacts::TRUTHY,
        TypeData::Object(object) if !object.is_empty() => TypeFacts::TRUTHY,
        TypeData::Union(union) => union.types.iter().fold(TypeFacts::NONE, |facts, ty| {
            facts | get_type_facts_worker(arena, *ty)
        }),
        TypeData::Never => TypeFacts::NONE,
        _ => TypeFacts::TRUTHY | TypeFacts::FALSY,
    }
}

// TODO: Simplify this when big int literals just support storing the actual value
fn bigint_literal_value_is_zero(value: &str) -> bool {
    let value = value
        .strip_prefix('-')
        .or_else(|| value.strip_prefix('+'))
        .unwrap_or(value)
        .to_ascii_lowercase();
    let digits = value
        .strip_prefix("0x")
        .or_else(|| value.strip_prefix("0o"))
        .or_else(|| value.strip_prefix("0b"))
        .unwrap_or(&value);
    digits.chars().all(|c| matches!(c, '0' | '_'))
}
