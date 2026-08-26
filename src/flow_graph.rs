use oxc_ast::AstKind;
use oxc_cfg::{
    BlockNodeId, EdgeType,
    graph::{
        algo::dominators::{Dominators, simple_fast},
        visit::EdgeRef,
    },
};
use oxc_semantic::{NodeId, SymbolId};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::LogicalOperator;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use crate::{
    checker::{Checker, NodeRef},
    limits::CONTROL_FLOW_GRAPH_MAX_DEPTH,
    program::ProgramId,
};

/// A condition outcome known to hold while evaluating a branch-local node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BranchEffect {
    pub(crate) controller: NodeId,
    pub(crate) branch_root: NodeId,
    pub(crate) assume_true: bool,
}

/// A write to a symbol at a specific source and control-flow location.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct WriteEvent {
    pub(crate) node_id: NodeId,
    pub(crate) block_id: BlockNodeId,
    pub(crate) span: Span,
}

/// The syntax that changes an evolving empty-array local.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ArrayMutationKind {
    AddCall(NodeId),
    IndexedAssignment(NodeId),
    ResetAssignment(NodeId),
}

/// An evolving-array mutation at a specific control-flow location.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ArrayMutationEvent {
    pub(crate) kind: ArrayMutationKind,
    pub(crate) block_id: BlockNodeId,
    pub(crate) span: Span,
}

/// Writes that determine an assignment-based flow type at a reference.
pub(crate) struct AssignmentFlow {
    pub(crate) seed: WriteEvent,
    pub(crate) loop_writes: SmallVec<[WriteEvent; 4]>,
    pub(crate) crosses_blocks: bool,
}

/// Lazily collected, type-independent flow effects for one program.
#[derive(Debug, Default)]
pub(crate) struct ProgramFlowGraph {
    effects_by_node: FxHashMap<NodeId, Box<[BranchEffect]>>,
    writes_by_symbol: FxHashMap<SymbolId, Box<[WriteEvent]>>,
    array_mutations_by_symbol: FxHashMap<SymbolId, Box<[ArrayMutationEvent]>>,
    array_mutation_spans_by_container: FxHashMap<(SymbolId, BlockNodeId), Box<[Span]>>,
    disabled_containers: FxHashSet<BlockNodeId>,
    dominators_by_entry: FxHashMap<BlockNodeId, Dominators<BlockNodeId>>,
}

impl ProgramFlowGraph {
    pub(crate) fn cached_effects(&self, node_id: NodeId) -> Option<&[BranchEffect]> {
        self.effects_by_node.get(&node_id).map(Box::as_ref)
    }

    pub(crate) fn cache_effects(&mut self, node_id: NodeId, effects: &[BranchEffect]) {
        self.effects_by_node
            .insert(node_id, effects.to_vec().into_boxed_slice());
    }

    pub(crate) fn cached_writes(&self, symbol_id: SymbolId) -> Option<&[WriteEvent]> {
        self.writes_by_symbol.get(&symbol_id).map(Box::as_ref)
    }

    pub(crate) fn cache_writes(&mut self, symbol_id: SymbolId, writes: &[WriteEvent]) {
        self.writes_by_symbol
            .insert(symbol_id, writes.to_vec().into_boxed_slice());
    }

    pub(crate) fn cached_array_mutations(
        &self,
        symbol_id: SymbolId,
    ) -> Option<&[ArrayMutationEvent]> {
        self.array_mutations_by_symbol
            .get(&symbol_id)
            .map(Box::as_ref)
    }

    pub(crate) fn cache_array_mutations(
        &mut self,
        symbol_id: SymbolId,
        mutations: &[ArrayMutationEvent],
    ) {
        self.array_mutations_by_symbol
            .insert(symbol_id, mutations.to_vec().into_boxed_slice());
    }
}

impl Checker<'_, '_> {
    pub(crate) fn flow_analysis_disabled(&self, node: NodeRef) -> bool {
        let container = flow_container_entry(self.cfg(node.program_id), self.cfg_id(node));
        self.flow_graph_cache
            .borrow()
            .get(&node.program_id)
            .is_some_and(|graph| graph.disabled_containers.contains(&container))
    }

    fn disable_flow_analysis(&self, node: NodeRef) {
        let container = flow_container_entry(self.cfg(node.program_id), self.cfg_id(node));

        self.flow_graph_cache
            .borrow_mut()
            .entry(node.program_id)
            .or_default()
            .disabled_containers
            .insert(container);
    }

    /// Return enclosing branch effects in outermost-to-innermost evaluation order.
    pub(crate) fn branch_effects(&self, node: NodeRef) -> SmallVec<[BranchEffect; 4]> {
        if let Some(effects) = self
            .flow_graph_cache
            .borrow()
            .get(&node.program_id)
            .and_then(|graph| graph.cached_effects(node.node_id))
        {
            return effects.iter().copied().collect();
        }

        let effects = self.collect_branch_effects(node);
        self.flow_graph_cache
            .borrow_mut()
            .entry(node.program_id)
            .or_default()
            .cache_effects(node.node_id, &effects);
        effects
    }

    /// Return symbol writes in source order, collecting their CFG locations once per checker.
    pub(crate) fn symbol_writes(
        &self,
        program_id: ProgramId,
        symbol_id: SymbolId,
    ) -> SmallVec<[WriteEvent; 4]> {
        if let Some(writes) = self
            .flow_graph_cache
            .borrow()
            .get(&program_id)
            .and_then(|graph| graph.cached_writes(symbol_id))
        {
            return writes.iter().copied().collect();
        }

        let mut writes = self
            .semantic(program_id)
            .symbol_references(symbol_id)
            .filter(|reference| reference.is_write())
            .map(|reference| {
                let node_id = reference.node_id();
                WriteEvent {
                    node_id,
                    block_id: self.cfg_id_in_program(program_id, node_id),
                    span: self.write_effect_span(program_id, node_id),
                }
            })
            .collect::<SmallVec<[WriteEvent; 4]>>();
        if let Some((declaration_id, declarator)) = self
            .variable_declarator_for_symbol(crate::checker::SymbolRef::new(program_id, symbol_id))
            && declarator.init.as_ref().is_some_and(|initializer| {
                matches!(
                    initializer,
                    oxc_ast::ast::Expression::BooleanLiteral(_)
                        | oxc_ast::ast::Expression::NullLiteral(_)
                        | oxc_ast::ast::Expression::NumericLiteral(_)
                        | oxc_ast::ast::Expression::StringLiteral(_)
                        | oxc_ast::ast::Expression::BigIntLiteral(_)
                )
            })
        {
            writes.push(WriteEvent {
                node_id: declaration_id,
                block_id: self.cfg_id_in_program(program_id, declaration_id),
                span: declarator.span,
            });
        }
        writes.sort_unstable_by_key(|write| write.span.end);

        self.flow_graph_cache
            .borrow_mut()
            .entry(program_id)
            .or_default()
            .cache_writes(symbol_id, &writes);
        writes
    }

    /// Return evolving-array mutations in source order, collecting their syntax once per checker.
    pub(crate) fn array_mutations(
        &self,
        program_id: ProgramId,
        symbol_id: SymbolId,
    ) -> SmallVec<[ArrayMutationEvent; 4]> {
        if let Some(mutations) = self
            .flow_graph_cache
            .borrow()
            .get(&program_id)
            .and_then(|graph| graph.cached_array_mutations(symbol_id))
        {
            return mutations.iter().copied().collect();
        }

        let mut mutations = self
            .semantic(program_id)
            .symbol_references(symbol_id)
            .filter_map(|reference| {
                self.array_mutation_for_reference(program_id, reference.node_id())
            })
            .collect::<SmallVec<[ArrayMutationEvent; 4]>>();
        mutations.sort_unstable_by_key(|mutation| mutation.span.end);

        self.flow_graph_cache
            .borrow_mut()
            .entry(program_id)
            .or_default()
            .cache_array_mutations(symbol_id, &mutations);
        mutations
    }

    pub(crate) fn evolving_array_flow_depth_exceeded(
        &self,
        node: NodeRef,
        symbol_id: SymbolId,
    ) -> bool {
        let container = flow_container_entry(self.cfg(node.program_id), self.cfg_id(node));
        if self
            .flow_graph_cache
            .borrow()
            .get(&node.program_id)
            .and_then(|graph| graph.cached_array_mutations(symbol_id))
            .is_none()
        {
            self.array_mutations(node.program_id, symbol_id);
        }

        let cfg = self.cfg(node.program_id);
        let query_start = self.nodes(node.program_id).kind(node.node_id).span().start;
        let mut cache = self.flow_graph_cache.borrow_mut();
        let graph = cache.entry(node.program_id).or_default();
        let key = (symbol_id, container);
        if !graph.array_mutation_spans_by_container.contains_key(&key) {
            let spans = graph
                .cached_array_mutations(symbol_id)
                .unwrap_or_default()
                .iter()
                .filter(|mutation| flow_container_entry(cfg, mutation.block_id) == container)
                .map(|mutation| mutation.span)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            graph.array_mutation_spans_by_container.insert(key, spans);
        }
        let spans = &graph.array_mutation_spans_by_container[&key];
        let preceding_mutations = spans.partition_point(|span| span.end <= query_start);
        let exceeded = preceding_mutations >= CONTROL_FLOW_GRAPH_MAX_DEPTH;
        drop(cache);
        if exceeded {
            self.disable_flow_analysis(node);
        }
        exceeded
    }

    fn array_mutation_for_reference(
        &self,
        program_id: ProgramId,
        reference_id: NodeId,
    ) -> Option<ArrayMutationEvent> {
        let nodes = self.nodes(program_id);
        let reference_span = nodes.kind(reference_id).span();
        let parent_id = nodes.parent_id(reference_id);

        if let AstKind::StaticMemberExpression(member) = nodes.kind(parent_id)
            && member.object.span() == reference_span
            && matches!(member.property.name.as_str(), "push" | "unshift")
        {
            let call_id = nodes.parent_id(parent_id);
            if let AstKind::CallExpression(call) = nodes.kind(call_id)
                && call.callee.span() == member.span
                && !call.arguments.is_empty()
            {
                return Some(ArrayMutationEvent {
                    kind: ArrayMutationKind::AddCall(call_id),
                    block_id: nodes.cfg_id(call_id),
                    span: call.span,
                });
            }
        }

        if let AstKind::ComputedMemberExpression(member) = nodes.kind(parent_id)
            && member.object.span() == reference_span
        {
            let assignment_id = nodes.parent_id(parent_id);
            if let AstKind::AssignmentExpression(assignment) = nodes.kind(assignment_id)
                && assignment.operator == oxc_syntax::operator::AssignmentOperator::Assign
                && assignment.left.span() == member.span
            {
                return Some(ArrayMutationEvent {
                    kind: ArrayMutationKind::IndexedAssignment(assignment_id),
                    block_id: nodes.cfg_id(assignment_id),
                    span: assignment.span,
                });
            }
        }

        if let AstKind::AssignmentExpression(assignment) = nodes.kind(parent_id)
            && assignment.operator == oxc_syntax::operator::AssignmentOperator::Assign
            && assignment.left.span() == reference_span
        {
            return Some(ArrayMutationEvent {
                kind: ArrayMutationKind::ResetAssignment(parent_id),
                block_id: nodes.cfg_id(parent_id),
                span: assignment.span,
            });
        }

        None
    }

    /// Find the linear or loop-carried writes that can determine a reference's flow type.
    pub(crate) fn assignment_flow(
        &self,
        node: NodeRef,
        symbol_id: SymbolId,
    ) -> Option<AssignmentFlow> {
        let nodes = self.nodes(node.program_id);
        let query_span = nodes.kind(node.node_id).span();
        let query_block = self.cfg_id(node);
        let writes = self.symbol_writes(node.program_id, symbol_id);
        if writes.is_empty() {
            return None;
        }

        if let Some(seed) = writes.iter().rev().find(|write| {
            write.span.end <= query_span.start
                && write.block_id == query_block
                && !matches!(nodes.kind(write.node_id), AstKind::VariableDeclarator(_))
        }) {
            return Some(AssignmentFlow {
                seed: *seed,
                loop_writes: SmallVec::new(),
                crosses_blocks: false,
            });
        }

        let cfg = self.cfg(node.program_id);
        let is_in_loop = cfg.graph().edge_references().any(|edge| {
            matches!(edge.weight(), EdgeType::Backedge)
                && cfg.is_reachable(edge.target(), query_block)
                && cfg.is_reachable(query_block, edge.source())
        });
        if !is_in_loop {
            return None;
        }
        let dominating_blocks = self.dominating_blocks(node.program_id, query_block)?;
        let seed = writes.iter().rev().find(|write| {
            write.span.end <= query_span.start && dominating_blocks.contains(&write.block_id)
        })?;

        let loop_writes = writes
            .iter()
            .copied()
            .filter(|write| {
                write.span.end > seed.span.end
                    && cfg.is_reachable(query_block, write.block_id)
                    && cfg.is_reachable(write.block_id, query_block)
            })
            .collect();

        Some(AssignmentFlow {
            seed: *seed,
            loop_writes,
            crosses_blocks: true,
        })
    }

    fn dominating_blocks(
        &self,
        program_id: ProgramId,
        block: BlockNodeId,
    ) -> Option<FxHashSet<BlockNodeId>> {
        let cfg = self.cfg(program_id);
        let entry = flow_container_entry(cfg, block);
        let mut cache = self.flow_graph_cache.borrow_mut();
        cache
            .entry(program_id)
            .or_default()
            .dominators_by_entry
            .entry(entry)
            .or_insert_with(|| simple_fast(cfg.graph(), entry))
            .dominators(block)
            .map(Iterator::collect)
    }
}

pub(crate) fn flow_container_entry(
    cfg: &oxc_cfg::ControlFlowGraph,
    block: BlockNodeId,
) -> BlockNodeId {
    cfg.graph()
        .edge_references()
        .filter(|edge| matches!(edge.weight(), EdgeType::NewFunction))
        .map(|edge| edge.target())
        .find(|entry| cfg.is_reachable(*entry, block))
        .or_else(|| {
            cfg.graph().node_indices().find(|candidate| {
                cfg.is_reachable(*candidate, block)
                    && cfg
                        .graph()
                        .edges_directed(*candidate, oxc_cfg::graph::Direction::Incoming)
                        .all(|edge| {
                            !matches!(
                                edge.weight(),
                                EdgeType::Normal
                                    | EdgeType::Jump
                                    | EdgeType::Backedge
                                    | EdgeType::Join
                            )
                        })
            })
        })
        .unwrap_or(block)
}

impl Checker<'_, '_> {
    fn write_effect_span(&self, program_id: ProgramId, node_id: NodeId) -> Span {
        let nodes = self.nodes(program_id);
        let node_span = nodes.kind(node_id).span();
        let parent_id = nodes.parent_id(node_id);
        match nodes.kind(parent_id) {
            AstKind::AssignmentExpression(assignment) if assignment.left.span() == node_span => {
                assignment.span
            }
            _ => node_span,
        }
    }

    fn collect_branch_effects(&self, node: NodeRef) -> SmallVec<[BranchEffect; 4]> {
        let nodes = self.nodes(node.program_id);
        let cfg = self.cfg(node.program_id);
        let query_block = self.cfg_id(node);
        let mut effects = SmallVec::new();
        let mut branch_root = node.node_id;

        for (ancestor_id, ancestor) in nodes.ancestors_enumerated(node.node_id) {
            let assume_true = match ancestor.kind() {
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Class(_) => {
                    break;
                }
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
                if effects.len() == CONTROL_FLOW_GRAPH_MAX_DEPTH {
                    self.disable_flow_analysis(node);
                    return SmallVec::new();
                }
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
}
