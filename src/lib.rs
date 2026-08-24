use oxc_ast::ast::{
    BindingPattern, ForStatementLeft, PropertyKey, TSType, TSTypeName, TSTypeQueryExprName,
    VariableDeclarator,
};
use oxc_semantic::SymbolId;
use oxc_span::{GetSpan, Span};

pub mod checker;
mod checker_impl;
mod flow;
mod flow_graph;
mod global_lib;
mod global_types;
mod infer;
mod intrinsics;
mod limits;
mod mapper;
mod printer;
pub mod program;
mod relations;
mod type_facts;
pub mod type_set;
pub mod types;

pub use global_lib::{LibTarget, StandardLibrarySelection, StandardLibrarySelectionError};
pub use types::*;

// TODO: Move all the utility functions to a separate module.

fn property_key_name_str<'a>(key: &PropertyKey<'a>) -> Option<&'a str> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.name.as_str()),
        PropertyKey::Identifier(identifier) => Some(identifier.name.as_str()),
        PropertyKey::NumericLiteral(literal) => literal.raw.as_ref().map(oxc_str::Str::as_str),
        PropertyKey::StringLiteral(literal) => Some(literal.value.as_str()),
        _ => None,
    }
}

fn index_type_to_property_name<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> Option<&'a str> {
    match arena.ty_kind(ty) {
        types::TyKind::StringLiteral(literal) => Some(literal.value),
        types::TyKind::NumberLiteral(literal) => literal.raw.as_ref().map(oxc_str::Str::as_str),
        types::TyKind::BooleanLiteral(value) => Some(if value { "true" } else { "false" }),
        types::TyKind::TemplateLiteral(template) if template.expressions.is_empty() => {
            Some(template.quasis[0].value)
        }
        types::TyKind::TypeReference(reference) if reference.is_bare() => Some(reference.name),
        types::TyKind::String => Some(arena.str("string")),
        types::TyKind::Number => Some(arena.str("number")),
        _ => None,
    }
}

fn ts_type_name_to_str<'a>(arena: CheckerArena<'a>, name: &TSTypeName<'a>) -> &'a str {
    match name {
        TSTypeName::IdentifierReference(identifier) => identifier.name.as_str(),
        TSTypeName::QualifiedName(qualified) => {
            let left = ts_type_name_to_str(arena, &qualified.left);
            arena.str(&format!("{}.{}", left, qualified.right.name))
        }
        TSTypeName::ThisExpression(_) => "this",
    }
}

fn is_empty_object_intersection(ty: &TSType<'_>) -> bool {
    matches!(
        ty,
        TSType::TSIntersectionType(intersection)
            if intersection.types.iter().any(|ty| {
                matches!(ty, TSType::TSTypeLiteral(type_literal) if type_literal.members.is_empty())
            })
    )
}

/// Convert a `typeof` query target into a lookup key when it can be resolved locally.
fn ts_type_query_expr_name_to_str<'a>(
    arena: CheckerArena<'a>,
    name: &TSTypeQueryExprName<'a>,
) -> Option<&'a str> {
    name.as_ts_type_name()
        .map(|name| ts_type_name_to_str(arena, name))
}

fn binding_pattern_symbol_id(pattern: &BindingPattern<'_>) -> Option<SymbolId> {
    match pattern {
        BindingPattern::BindingIdentifier(identifier) => identifier.symbol_id.get(),
        _ => None,
    }
}

fn binding_pattern_default_initializer_symbol_id(
    pattern: &BindingPattern<'_>,
    initializer_span: Span,
) -> Option<SymbolId> {
    match pattern {
        BindingPattern::BindingIdentifier(_) => None,
        BindingPattern::ObjectPattern(object) => object
            .properties
            .iter()
            .find_map(|property| {
                binding_pattern_default_initializer_symbol_id(&property.value, initializer_span)
            })
            .or_else(|| {
                object.rest.as_ref().and_then(|rest| {
                    binding_pattern_default_initializer_symbol_id(&rest.argument, initializer_span)
                })
            }),
        BindingPattern::ArrayPattern(array) => array
            .elements
            .iter()
            .flatten()
            .find_map(|element| {
                binding_pattern_default_initializer_symbol_id(element, initializer_span)
            })
            .or_else(|| {
                array.rest.as_ref().and_then(|rest| {
                    binding_pattern_default_initializer_symbol_id(&rest.argument, initializer_span)
                })
            }),
        BindingPattern::AssignmentPattern(assignment) => {
            if assignment.right.span() == initializer_span {
                binding_pattern_symbol_id(&assignment.left)
            } else {
                binding_pattern_default_initializer_symbol_id(&assignment.left, initializer_span)
            }
        }
    }
}

fn for_statement_left_contains_declarator(
    left: &ForStatementLeft<'_>,
    target: &VariableDeclarator<'_>,
) -> bool {
    match left {
        ForStatementLeft::VariableDeclaration(declaration) => declaration
            .declarations
            .iter()
            .any(|declarator| declarator.span == target.span),
        _ => false,
    }
}

fn index_signature_key_types<'a>(
    arena: CheckerArena<'a>,
    constraint: Ty<'a>,
) -> Option<Vec<Ty<'a>>> {
    match arena.ty_kind(constraint) {
        types::TyKind::String => Some(vec![Ty::String]),
        types::TyKind::Number => Some(vec![Ty::Number]),
        types::TyKind::Symbol => Some(vec![Ty::Symbol]),
        types::TyKind::Union(union) => {
            let mut key_types = Vec::new();
            for ty in &union.types {
                let keys = index_signature_key_types(arena, *ty)?;
                for key in keys {
                    if !key_types.contains(&key) {
                        key_types.push(key);
                    }
                }
            }
            Some(key_types)
        }
        _ => None,
    }
}

#[cfg(feature = "bench")]
#[doc(hidden)]
pub mod benchmark_support;

#[cfg(all(test, any(feature = "conformance", feature = "conformance-tsc")))]
mod conformance;

#[cfg(test)]
#[path = "lib_test.rs"]
mod lib_test;
