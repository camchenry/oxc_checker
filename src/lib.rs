use oxc_ast::{
    AstKind,
    ast::{
        BindingPattern, Expression, ForStatementLeft, PropertyKey, TSType, TSTypeName,
        TSTypeQueryExprName, VariableDeclarator,
    },
};
use oxc_semantic::SymbolId;
use oxc_span::{GetSpan, Span};

pub mod checker;
mod checker_impl;
mod evolving_arrays;
mod flow;
mod global_lib;
mod global_types;
mod infer;
mod limits;
mod mapper;
pub mod program;
mod relations;
mod type_facts;
pub mod type_set;
pub mod types;

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
    match arena.type_data(ty) {
        types::TypeData::StringLiteral(literal) => {
            Some(string_literal_type_to_property_name(arena, literal.value))
        }
        types::TypeData::NumberLiteral(literal) => literal.raw.as_ref().map(oxc_str::Str::as_str),
        types::TypeData::BooleanLiteral(value) => Some(if value { "true" } else { "false" }),
        types::TypeData::TemplateLiteral(template) if template.expressions.is_empty() => {
            Some(template.quasis[0].value)
        }
        types::TypeData::TypeReference(reference) if reference.is_bare() => Some(reference.name),
        types::TypeData::String => Some(arena.str("string")),
        types::TypeData::Number => Some(arena.str("number")),
        _ => None,
    }
}

fn string_literal_type_to_property_name<'a>(arena: CheckerArena<'a>, value: &'a str) -> &'a str {
    if value.len() >= 2
        && ((value.starts_with('"') && value.ends_with('"'))
            || (value.starts_with('\'') && value.ends_with('\'')))
    {
        arena.str(&value[1..value.len() - 1])
    } else {
        value
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

fn is_mapped_empty_object_intersection(ty: &TSType<'_>) -> bool {
    let TSType::TSIntersectionType(intersection) = ty else {
        return false;
    };

    let mut has_mapped = false;
    let mut has_empty_object = false;
    for ty in &intersection.types {
        match ty {
            TSType::TSMappedType(_) => has_mapped = true,
            TSType::TSTypeLiteral(type_literal) if type_literal.members.is_empty() => {
                has_empty_object = true;
            }
            _ => return false,
        }
    }

    has_mapped && has_empty_object
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
    match name {
        TSTypeQueryExprName::IdentifierReference(identifier) => Some(identifier.name.as_str()),
        TSTypeQueryExprName::QualifiedName(qualified) => {
            let left = ts_type_name_to_str(arena, &qualified.left);
            Some(arena.str(&format!("{}.{}", left, qualified.right.name)))
        }
        TSTypeQueryExprName::ThisExpression(_) => Some("this"),
        TSTypeQueryExprName::TSImportType(_) => None,
    }
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

fn push_type_parameter_names<'a>(
    names: &mut Vec<&'a str>,
    type_parameters: Option<&oxc_ast::ast::TSTypeParameterDeclaration<'a>>,
) {
    if let Some(type_parameters) = type_parameters {
        names.extend(
            type_parameters
                .params
                .iter()
                .map(|parameter| parameter.name.name.as_str()),
        );
    }
}

fn tuple_index_from_expression(expression: &Expression<'_>) -> Option<usize> {
    let Expression::NumericLiteral(literal) = expression else {
        return None;
    };
    if !literal.value.is_finite() || literal.value < 0.0 || literal.value.fract() != 0.0 {
        return None;
    }
    if literal.value > usize::MAX as f64 {
        return None;
    }
    Some(literal.value as usize)
}

fn tuple_index_from_index_type<'a>(arena: CheckerArena<'a>, index_type: Ty<'a>) -> Option<usize> {
    let types::TypeData::NumberLiteral(literal) = arena.type_data(index_type) else {
        return None;
    };
    if !literal.value.is_finite() || literal.value < 0.0 || literal.value.fract() != 0.0 {
        return None;
    }
    if literal.value > usize::MAX as f64 {
        return None;
    }
    Some(literal.value as usize)
}

fn tuple_element_type_at_index<'a>(
    arena: CheckerArena<'a>,
    object_type: Ty<'a>,
    index: usize,
) -> Option<Ty<'a>> {
    let types::TypeData::Tuple(tuple) = arena.type_data(object_type) else {
        return None;
    };

    let mut current_index = 0;
    for element in &tuple.elements {
        match element {
            TupleElement::Regular(ty) | TupleElement::Optional(ty) => {
                if current_index == index {
                    return Some(*ty);
                }
                current_index += 1;
            }
            TupleElement::Rest(ty) => {
                if index >= current_index {
                    return Some(ty.array_element_type(arena).unwrap_or(*ty));
                }
            }
        }
    }

    Some(Ty::undefined())
}

fn index_signature_key_types<'a>(
    arena: CheckerArena<'a>,
    constraint: Ty<'a>,
) -> Option<Vec<Ty<'a>>> {
    match arena.type_data(constraint) {
        types::TypeData::String => Some(vec![Ty::string()]),
        types::TypeData::Number => Some(vec![Ty::number()]),
        types::TypeData::Symbol => Some(vec![Ty::symbol()]),
        types::TypeData::Union(union) => {
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

#[doc(hidden)]
pub mod benchmark_support {
    use std::collections::BTreeMap;

    use crate::checker::{Checker, CheckerBuilder, NodeRef};

    use super::{AstKind, program};
    use oxc_semantic::NodeId;

    pub struct CheckPlan {
        program_id: program::ProgramId,
        queries: Vec<CheckQuery>,
    }

    pub struct CheckStats {
        pub checked_types: usize,
        pub registered_types: usize,
        pub type_kinds: Vec<(&'static str, usize)>,
    }

    impl CheckPlan {
        #[must_use]
        pub const fn query_count(&self) -> usize {
            self.queries.len()
        }
    }

    #[derive(Clone, Copy)]
    enum CheckQueryKind {
        Location,
        TypeAlias,
    }

    #[derive(Clone, Copy)]
    struct CheckQuery {
        node_id: NodeId,
        kind: CheckQueryKind,
    }

    #[must_use]
    pub fn check_plan(
        store: &program::ProgramStore<'_>,
        program_id: program::ProgramId,
    ) -> CheckPlan {
        let queries = store
            .entry(program_id)
            .map(|entry| {
                entry
                    .semantic()
                    .nodes()
                    .iter_enumerated()
                    .filter_map(|(node_id, node)| {
                        let kind = match node.kind() {
                            AstKind::BindingIdentifier(_)
                            | AstKind::IdentifierReference(_)
                            | AstKind::IdentifierName(_)
                            | AstKind::TSPropertySignature(_)
                            | AstKind::TSMethodSignature(_)
                            | AstKind::TSThisParameter(_)
                            | AstKind::FormalParameter(_)
                            | AstKind::FormalParameterRest(_)
                            | AstKind::StaticMemberExpression(_)
                            | AstKind::ObjectProperty(_)
                            | AstKind::MethodDefinition(_)
                            | AstKind::PropertyDefinition(_) => CheckQueryKind::Location,
                            AstKind::TSTypeAliasDeclaration(_) => CheckQueryKind::TypeAlias,
                            _ => return None,
                        };
                        Some(CheckQuery { node_id, kind })
                    })
                    .collect()
            })
            .unwrap_or_default();

        CheckPlan {
            program_id,
            queries,
        }
    }

    /// Build reusable checker query plans for every non-library file in a program store.
    #[must_use]
    pub fn check_plans(store: &program::ProgramStore<'_>) -> Vec<CheckPlan> {
        store
            .entries()
            .iter()
            .filter(|entry| !entry.is_lib())
            .map(|entry| check_plan(store, entry.id()))
            .collect()
    }

    /// Run checker type queries over an already parsed and semantically built program.
    ///
    /// This intentionally excludes parsing, semantic analysis, file IO, and type string rendering
    /// so Criterion benchmarks can isolate checker work.
    #[must_use]
    pub fn check_program(
        store: &program::ProgramStore<'_>,
        program_id: program::ProgramId,
    ) -> usize {
        let plan = check_plan(store, program_id);
        check_program_with_plan(store, &plan)
    }

    #[must_use]
    pub fn check_program_with_plan(store: &program::ProgramStore<'_>, plan: &CheckPlan) -> usize {
        let checker = CheckerBuilder::new().build(store);
        run_check_plan(&checker, plan)
    }

    #[must_use]
    pub fn check_program_with_plan_stats(
        store: &program::ProgramStore<'_>,
        plan: &CheckPlan,
    ) -> CheckStats {
        let checker = CheckerBuilder::new().build(store);
        let checked_types = run_check_plan(&checker, plan);
        let mut type_kinds = BTreeMap::new();
        for ty in checker.types() {
            let kind = match checker.arena.type_data(ty) {
                crate::types::TypeData::TypeReference(reference) if reference.target.is_some() => {
                    "TyTypeReference(symbol)"
                }
                crate::types::TypeData::TypeReference(_) => "TyTypeReference(name)",
                _ => ty.enum_variant_name(checker.arena),
            };
            *type_kinds.entry(kind).or_default() += 1;
        }
        CheckStats {
            checked_types,
            registered_types: checker.type_count(),
            type_kinds: type_kinds.into_iter().collect(),
        }
    }

    fn run_check_plan(checker: &crate::checker::CheckerReturn<'_, '_>, plan: &CheckPlan) -> usize {
        let store = checker.store;
        let Some(entry) = store.entry(plan.program_id) else {
            return 0;
        };

        plan.queries
            .iter()
            .filter_map(|query| {
                let node_ref = NodeRef::new(plan.program_id, query.node_id);
                let node = entry.semantic().nodes().kind(query.node_id);
                let ty = match node {
                    _ if matches!(query.kind, CheckQueryKind::Location) => {
                        checker.get_type_at_location(node_ref)
                    }
                    AstKind::TSTypeAliasDeclaration(alias)
                        if matches!(query.kind, CheckQueryKind::TypeAlias) =>
                    {
                        checker.get_type_of_type_alias_declaration(plan.program_id, alias)
                    }
                    _ => return None,
                };

                Some(usize::from(!ty.is_none()))
            })
            .sum()
    }
}

#[cfg(all(test, any(feature = "conformance", feature = "conformance-tsc")))]
mod conformance;

#[cfg(test)]
#[path = "lib_test.rs"]
mod lib_test;
