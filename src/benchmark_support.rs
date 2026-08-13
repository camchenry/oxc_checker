use std::collections::BTreeMap;

use crate::checker::{Checker, CheckerBuilder, NodeRef};

use oxc_ast::AstKind;
use oxc_semantic::NodeId;

use super::program;

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
pub fn check_plan(store: &program::ProgramStore<'_>, program_id: program::ProgramId) -> CheckPlan {
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
pub fn check_program(store: &program::ProgramStore<'_>, program_id: program::ProgramId) -> usize {
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
