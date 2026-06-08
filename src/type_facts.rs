use bitflags::bitflags;

use crate::types::Ty;

bitflags! {
    /// Minimal facts about the possible runtime values of a type.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) struct TypeFacts: u8 {
        const NONE = 0;
        const TRUTHY = 1 << 0;
        const FALSY = 1 << 1;
    }
}

pub(crate) fn get_logical_not_type(ty: Ty<'_>) -> Ty<'_> {
    match get_type_facts(ty, TypeFacts::TRUTHY | TypeFacts::FALSY) {
        TypeFacts::TRUTHY => Ty::boolean_false(),
        TypeFacts::FALSY => Ty::boolean_true(),
        _ => Ty::boolean(),
    }
}

pub(crate) fn get_type_facts(ty: Ty<'_>, mask: TypeFacts) -> TypeFacts {
    get_type_facts_worker(ty, mask) & mask
}

fn get_type_facts_worker(ty: Ty<'_>, _caller_only_needs: TypeFacts) -> TypeFacts {
    match ty {
        Ty::String | Ty::Number | Ty::Boolean | Ty::Bigint | Ty::Any | Ty::Unknown => {
            TypeFacts::TRUTHY | TypeFacts::FALSY
        }
        Ty::StringLiteral(literal) => {
            if string_literal_value_is_empty(literal.value) {
                TypeFacts::FALSY
            } else {
                TypeFacts::TRUTHY
            }
        }
        Ty::NumberLiteral(literal) => {
            if literal.value == 0.0 {
                TypeFacts::FALSY
            } else {
                TypeFacts::TRUTHY
            }
        }
        Ty::BooleanLiteral(value) => {
            if value {
                TypeFacts::TRUTHY
            } else {
                TypeFacts::FALSY
            }
        }
        Ty::BigIntLiteral(literal) => {
            if bigint_literal_value_is_zero(literal.value) {
                TypeFacts::FALSY
            } else {
                TypeFacts::TRUTHY
            }
        }
        Ty::Undefined | Ty::Null | Ty::Void => TypeFacts::FALSY,
        Ty::Symbol
        | Ty::UniqueSymbol(_)
        | Ty::PrimitiveObject
        | Ty::ModuleNamespace(_)
        | Ty::Function(_)
        | Ty::Array(_)
        | Ty::Tuple(_)
        | Ty::TypeQuery(_) => TypeFacts::TRUTHY,
        Ty::Object(object) if !object.is_empty() => TypeFacts::TRUTHY,
        Ty::Union(union) => union.types.iter().fold(TypeFacts::NONE, |facts, ty| {
            facts | get_type_facts_worker(*ty, _caller_only_needs)
        }),
        Ty::Never => TypeFacts::NONE,
        _ => TypeFacts::TRUTHY | TypeFacts::FALSY,
    }
}

fn string_literal_value_is_empty(value: &str) -> bool {
    let unquoted = value
        .strip_prefix('\'')
        .and_then(|value| value.strip_suffix('\''))
        .or_else(|| {
            value
                .strip_prefix('"')
                .and_then(|value| value.strip_suffix('"'))
        })
        .unwrap_or(value);
    unquoted.is_empty()
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
