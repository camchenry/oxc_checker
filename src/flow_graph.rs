use std::collections::HashMap;

use oxc_ast::AstKind;
use oxc_semantic::NodeId;
use oxc_span::GetSpan;
use oxc_syntax::operator::LogicalOperator;
use smallvec::SmallVec;

use crate::checker::{CheckerReturn, NodeRef};

/// A condition outcome known to hold while evaluating a branch-local node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BranchEffect {
    pub(crate) controller: NodeId,
    pub(crate) branch_root: NodeId,
    pub(crate) assume_true: bool,
}

/// Lazily collected, type-independent flow effects for one program.
#[derive(Debug, Default)]
pub(crate) struct ProgramFlowGraph {
    effects_by_node: HashMap<NodeId, Box<[BranchEffect]>>,
}

impl ProgramFlowGraph {
    pub(crate) fn cached_effects(&self, node_id: NodeId) -> Option<&[BranchEffect]> {
        self.effects_by_node.get(&node_id).map(Box::as_ref)
    }

    pub(crate) fn cache_effects(&mut self, node_id: NodeId, effects: &[BranchEffect]) {
        self.effects_by_node
            .insert(node_id, effects.to_vec().into_boxed_slice());
    }
}

/// Return enclosing branch effects in outermost-to-innermost evaluation order.
pub(crate) fn branch_effects(
    checker: &CheckerReturn<'_, '_>,
    node: NodeRef,
) -> SmallVec<[BranchEffect; 4]> {
    if let Some(effects) = checker
        .flow_graph_cache
        .borrow()
        .get(&node.program_id)
        .and_then(|graph| graph.cached_effects(node.node_id))
    {
        return effects.iter().copied().collect();
    }

    let effects = collect_branch_effects(checker, node);
    checker
        .flow_graph_cache
        .borrow_mut()
        .entry(node.program_id)
        .or_default()
        .cache_effects(node.node_id, &effects);
    effects
}

fn collect_branch_effects(
    checker: &CheckerReturn<'_, '_>,
    node: NodeRef,
) -> SmallVec<[BranchEffect; 4]> {
    let nodes = checker.nodes(node.program_id);
    let Some(cfg) = checker.semantic(node.program_id).cfg() else {
        return SmallVec::new();
    };
    let query_block = nodes.cfg_id(node.node_id);
    let mut effects = SmallVec::new();
    let mut branch_root = node.node_id;

    for (ancestor_id, ancestor) in nodes.ancestors_enumerated(node.node_id) {
        let assume_true = match ancestor.kind() {
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Class(_) => break,
            AstKind::IfStatement(if_statement) => {
                let branch_span = nodes.kind(branch_root).span();
                if branch_span == if_statement.consequent.span() {
                    Some(true)
                } else if if_statement
                    .alternate
                    .as_ref()
                    .is_some_and(|alternate| branch_span == alternate.span())
                {
                    Some(false)
                } else {
                    None
                }
            }
            AstKind::ConditionalExpression(conditional) => {
                let branch_span = nodes.kind(branch_root).span();
                if branch_span == conditional.consequent.span() {
                    Some(true)
                } else if branch_span == conditional.alternate.span() {
                    Some(false)
                } else {
                    None
                }
            }
            AstKind::LogicalExpression(logical) => {
                let branch_span = nodes.kind(branch_root).span();
                if branch_span != logical.right.span() {
                    None
                } else {
                    match logical.operator {
                        LogicalOperator::And => Some(true),
                        LogicalOperator::Or => Some(false),
                        LogicalOperator::Coalesce => None,
                    }
                }
            }
            _ => None,
        };

        if let Some(assume_true) = assume_true {
            let branch_block = nodes.cfg_id(branch_root);
            if cfg.is_reachable(branch_block, query_block) {
                effects.push(BranchEffect {
                    controller: ancestor_id,
                    branch_root,
                    assume_true,
                });
            }
        }
        branch_root = ancestor_id;
    }

    effects.reverse();
    effects
}

#[cfg(test)]
pub(crate) fn legacy_branch_effects(
    checker: &CheckerReturn<'_, '_>,
    node: NodeRef,
) -> SmallVec<[BranchEffect; 4]> {
    let nodes = checker.nodes(node.program_id);
    let query_span = nodes.kind(node.node_id).span();
    let mut effects = SmallVec::new();
    let mut branch_root = node.node_id;

    for (ancestor_id, ancestor) in nodes.ancestors_enumerated(node.node_id) {
        let assume_true = match ancestor.kind() {
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Class(_) => break,
            AstKind::IfStatement(if_statement) => {
                if if_statement
                    .consequent
                    .span()
                    .contains_inclusive(query_span)
                {
                    Some(true)
                } else if if_statement
                    .alternate
                    .as_ref()
                    .is_some_and(|alternate| alternate.span().contains_inclusive(query_span))
                {
                    Some(false)
                } else {
                    None
                }
            }
            AstKind::ConditionalExpression(conditional) => {
                if conditional.consequent.span().contains_inclusive(query_span) {
                    Some(true)
                } else if conditional.alternate.span().contains_inclusive(query_span) {
                    Some(false)
                } else {
                    None
                }
            }
            AstKind::LogicalExpression(logical) => {
                if !logical.right.span().contains_inclusive(query_span) {
                    None
                } else {
                    match logical.operator {
                        LogicalOperator::And => Some(true),
                        LogicalOperator::Or => Some(false),
                        LogicalOperator::Coalesce => None,
                    }
                }
            }
            _ => None,
        };

        if let Some(assume_true) = assume_true {
            effects.push(BranchEffect {
                controller: ancestor_id,
                branch_root,
                assume_true,
            });
        }
        branch_root = ancestor_id;
    }

    effects.reverse();
    effects
}
