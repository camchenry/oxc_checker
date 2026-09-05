use std::collections::VecDeque;

use oxc_ast::{
    AstKind,
    ast::{
        ArrayExpression, ChainElement, Expression, LogicalExpression, SimpleAssignmentTarget,
        StaticMemberExpression,
    },
};
use oxc_cfg::{
    BlockNodeId, EdgeType,
    graph::{Direction, visit::EdgeRef},
};
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{AssignmentOperator, BinaryOperator, LogicalOperator, UnaryOperator};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    checker::{Checker, NodeRef, SymbolRef},
    checker_impl::CheckMode,
    flow_graph::{self, ArrayMutationKind, BranchEffect},
    program::ProgramId,
    type_set::UnionAccumulator,
    types::TypeErrorKind,
    types::{TupleElement, Ty, TyKind, TyTypePredicate},
};

#[derive(Clone, Copy)]
enum EvolvingArrayChange<'a> {
    Add(Ty<'a>),
    Reset(Ty<'a>),
}

/// String witnesses supported by JavaScript's `typeof` operator.
#[derive(Clone, Copy, Eq, PartialEq)]
enum TypeofWitness {
    String,
    Number,
    Boolean,
    Bigint,
    Undefined,
    Object,
    Function,
}

impl TypeofWitness {
    /// Convert a string-literal operand in a `typeof` comparison to a known witness.
    fn from_literal(value: &str) -> Option<Self> {
        match value {
            "string" => Some(Self::String),
            "number" => Some(Self::Number),
            "boolean" => Some(Self::Boolean),
            "bigint" => Some(Self::Bigint),
            "undefined" => Some(Self::Undefined),
            "object" => Some(Self::Object),
            "function" => Some(Self::Function),
            _ => None,
        }
    }
}

/// Return the type of a reference after applying currently supported flow facts.
impl<'a> Checker<'a, '_> {
    pub(crate) fn get_flow_type_of_reference(
        &self,
        node: NodeRef,
        symbol: SymbolRef,
        base_type: Ty<'a>,
    ) -> Ty<'a> {
        if symbol.program_id != node.program_id {
            return base_type;
        }
        if self.flow_analysis_disabled(node) {
            return self.ty.error(TypeErrorKind::ControlFlowGraphDepthExceeded);
        }

        let mut narrowed_type = self
            .evolving_array_flow_type(node, symbol, base_type)
            .unwrap_or(base_type);
        if self.flow_analysis_disabled(node) {
            return self.ty.error(TypeErrorKind::ControlFlowGraphDepthExceeded);
        }
        for effect in self.branch_effects(node) {
            let Some(condition) = self.branch_effect_condition(node.program_id, effect) else {
                continue;
            };
            let candidate_type = self.narrow_by_condition(
                node,
                symbol,
                narrowed_type,
                condition,
                effect.assume_true,
            );
            if candidate_type == narrowed_type {
                continue;
            }
            if self.intervening_write_invalidates(
                node,
                symbol,
                effect,
                condition.span(),
                candidate_type,
            ) {
                continue;
            }
            narrowed_type = candidate_type;
        }
        if self.flow_analysis_disabled(node) {
            return self.ty.error(TypeErrorKind::ControlFlowGraphDepthExceeded);
        }

        self.assignment_flow_type(node, symbol, narrowed_type)
            .unwrap_or(narrowed_type)
    }

    /// Return the element type for an empty array literal in expression typing.
    pub(crate) fn empty_array_literal_element_type(
        &self,
        program_id: ProgramId,
        array_expression: &'a ArrayExpression<'a>,
        node_id: Option<oxc_semantic::NodeId>,
    ) -> Ty<'a> {
        if self.is_direct_empty_array_variable_initializer(program_id, array_expression, node_id) {
            self.ty.any()
        } else {
            self.ty.never()
        }
    }

    fn evolving_array_flow_type(
        &self,
        node: NodeRef,
        symbol: SymbolRef,
        base_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        let (_declaration_id, declarator) = self.variable_declarator_for_symbol(symbol)?;
        if declarator.type_annotation.is_some()
            || !declarator
                .init
                .as_ref()
                .is_some_and(expression_is_empty_array_literal)
            || self.node_kind(node).span().start <= declarator.span.start
        {
            return None;
        }
        if self.evolving_array_flow_depth_exceeded(node, symbol.symbol_id) {
            return Some(self.ty.error(TypeErrorKind::ControlFlowGraphDepthExceeded));
        }
        if self.is_evolving_array_operation_target(node) {
            return Some(self.ty.array(self.ty.any()));
        }

        let empty_element_type = self.finalized_empty_element_type(base_type);
        let mut changes_by_block: FxHashMap<_, Vec<_>> = FxHashMap::default();
        for mutation in self.array_mutations(symbol.program_id, symbol.symbol_id) {
            if let Some(change) = self.evolving_array_change(symbol.program_id, mutation.kind) {
                changes_by_block
                    .entry(mutation.block_id)
                    .or_default()
                    .push((mutation.span, change));
            }
        }
        for changes in changes_by_block.values_mut() {
            changes.sort_unstable_by_key(|(span, _)| span.end);
        }

        let element_type = self.evolving_array_element_at_reference(node, &changes_by_block)?;
        Some(self.ty.array(if element_type.is_never() {
            empty_element_type
        } else {
            element_type
        }))
    }

    fn is_evolving_array_operation_target(&self, node: NodeRef) -> bool {
        let nodes = self.nodes(node.program_id);
        let reference_span = nodes.kind(node.node_id).span();
        let parent_id = nodes.parent_id(node.node_id);
        match nodes.kind(parent_id) {
            AstKind::StaticMemberExpression(member) if member.object.span() == reference_span => {
                member.property.name == "length"
                    || matches!(member.property.name.as_str(), "push" | "unshift")
                        && matches!(
                            nodes.kind(nodes.parent_id(parent_id)),
                            AstKind::CallExpression(call) if call.callee.span() == member.span
                        )
            }
            AstKind::ComputedMemberExpression(member) if member.object.span() == reference_span => {
                matches!(
                    nodes.kind(nodes.parent_id(parent_id)),
                    AstKind::AssignmentExpression(assignment)
                        if assignment.operator == AssignmentOperator::Assign
                            && assignment.left.span() == member.span
                )
            }
            _ => false,
        }
    }

    fn evolving_array_element_at_reference(
        &self,
        node: NodeRef,
        changes_by_block: &FxHashMap<BlockNodeId, Vec<(Span, EvolvingArrayChange<'a>)>>,
    ) -> Option<Ty<'a>> {
        const MAX_FLOW_UPDATES: usize = 10_000;

        let nodes = self.nodes(node.program_id);
        let cfg = self.cfg(node.program_id);
        let query_block = nodes.cfg_id(node.node_id);
        let entry = flow_graph::flow_container_entry(cfg, query_block);

        let mut outputs = FxHashMap::default();
        let mut pending = VecDeque::from([entry]);
        let mut queued = FxHashSet::default();
        queued.insert(entry);
        let mut updates = 0;
        while let Some(block) = pending.pop_front() {
            queued.remove(&block);
            let Some(mut element_type) =
                self.evolving_array_block_input(cfg, entry, block, &outputs)
            else {
                continue;
            };
            if let Some(changes) = changes_by_block.get(&block) {
                for (_, change) in changes {
                    element_type = self.apply_evolving_array_change(element_type, *change);
                }
            }
            if outputs.get(&block).copied() == Some(element_type) {
                continue;
            }
            outputs.insert(block, element_type);
            updates += 1;
            if updates > MAX_FLOW_UPDATES {
                return None;
            }
            for edge in cfg.graph().edges_directed(block, Direction::Outgoing) {
                if follows_value_flow(edge.weight()) && queued.insert(edge.target()) {
                    pending.push_back(edge.target());
                }
            }
        }

        let mut element_type =
            self.evolving_array_block_input(cfg, entry, query_block, &outputs)?;
        let query_start = nodes.kind(node.node_id).span().start;
        if let Some(changes) = changes_by_block.get(&query_block) {
            for (span, change) in changes {
                if span.end > query_start {
                    break;
                }
                element_type = self.apply_evolving_array_change(element_type, *change);
            }
        }
        Some(element_type)
    }

    fn evolving_array_block_input(
        &self,
        cfg: &oxc_cfg::ControlFlowGraph,
        entry: BlockNodeId,
        block: BlockNodeId,
        outputs: &FxHashMap<BlockNodeId, Ty<'a>>,
    ) -> Option<Ty<'a>> {
        if block == entry {
            return Some(self.ty.never());
        }
        let mut predecessor_types = UnionAccumulator::new(self.arena());
        predecessor_types.extend(
            cfg.graph()
                .edges_directed(block, Direction::Incoming)
                .filter(|edge| follows_value_flow(edge.weight()))
                .filter_map(|edge| outputs.get(&edge.source()).copied()),
        );
        predecessor_types.try_build()
    }
}

fn follows_value_flow(edge: &EdgeType) -> bool {
    matches!(
        edge,
        EdgeType::Normal
            | EdgeType::Jump
            | EdgeType::Backedge
            | EdgeType::NewFunction
            | EdgeType::Join
    )
}

impl<'a> Checker<'a, '_> {
    fn apply_evolving_array_change(
        &self,
        current: Ty<'a>,
        change: EvolvingArrayChange<'a>,
    ) -> Ty<'a> {
        match change {
            EvolvingArrayChange::Add(ty) => self.ty.union([current, ty]),
            EvolvingArrayChange::Reset(ty) => ty,
        }
    }

    fn evolving_array_change(
        &self,
        program_id: ProgramId,
        kind: ArrayMutationKind,
    ) -> Option<EvolvingArrayChange<'a>> {
        let nodes = self.nodes(program_id);
        match kind {
            ArrayMutationKind::AddCall(call_id) => {
                let AstKind::CallExpression(call) = nodes.kind(call_id) else {
                    return None;
                };
                let mut element_types = UnionAccumulator::new(self.arena());
                element_types.extend(
                    call.arguments
                        .iter()
                        .filter_map(|argument| argument.as_expression())
                        .map(|argument| {
                            self.get_type_of_expression_with_node(
                                program_id,
                                argument,
                                Some(call_id),
                                CheckMode::NONE,
                            )
                        }),
                );
                element_types.try_build().map(EvolvingArrayChange::Add)
            }
            ArrayMutationKind::IndexedAssignment(assignment_id) => {
                let AstKind::AssignmentExpression(assignment) = nodes.kind(assignment_id) else {
                    return None;
                };
                Some(EvolvingArrayChange::Add(
                    self.get_type_of_expression_with_node(
                        program_id,
                        &assignment.right,
                        Some(assignment_id),
                        CheckMode::CONTEXT_FREE,
                    ),
                ))
            }
            ArrayMutationKind::ResetAssignment(assignment_id) => {
                let AstKind::AssignmentExpression(assignment) = nodes.kind(assignment_id) else {
                    return None;
                };
                let assigned_type = self.get_type_of_expression_with_node(
                    program_id,
                    &assignment.right,
                    Some(assignment_id),
                    CheckMode::CONTEXT_FREE,
                );
                match self.ty_kind(assigned_type) {
                    TyKind::Array(array) => Some(EvolvingArrayChange::Reset(array.element_type)),
                    TyKind::Tuple(tuple) => Some(EvolvingArrayChange::Reset(self.ty.union(
                        tuple.elements.iter().map(|element| match element {
                            TupleElement::Regular(ty)
                            | TupleElement::Rest(ty)
                            | TupleElement::Optional(ty) => *ty,
                        }),
                    ))),
                    _ => None,
                }
            }
        }
    }

    fn is_direct_empty_array_variable_initializer(
        &self,
        program_id: ProgramId,
        array_expression: &'a ArrayExpression<'a>,
        node_id: Option<oxc_semantic::NodeId>,
    ) -> bool {
        let Some(node_id) = node_id else {
            return false;
        };
        let AstKind::VariableDeclarator(declarator) =
            self.node_kind(NodeRef::new(program_id, node_id))
        else {
            return false;
        };
        declarator
            .init
            .as_ref()
            .is_some_and(|initializer| initializer.span() == array_expression.span)
    }

    fn finalized_empty_element_type(&self, base_type: Ty<'a>) -> Ty<'a> {
        match self.ty_kind(base_type) {
            TyKind::Array(array) if array.element_type.is_never() => self.ty.any(),
            TyKind::Array(array) => array.element_type,
            _ => self.ty.any(),
        }
    }
}

fn expression_is_empty_array_literal(expression: &Expression<'_>) -> bool {
    matches!(expression, Expression::ArrayExpression(array) if array.elements.is_empty())
}

impl<'a> Checker<'a, '_> {
    pub(crate) fn get_flow_type_of_static_member_reference(
        &self,
        program_id: ProgramId,
        member: &StaticMemberExpression<'_>,
        base_type: Ty<'a>,
    ) -> Ty<'a> {
        let Expression::Identifier(identifier) = &member.object else {
            return base_type;
        };
        let Some(symbol) = self.symbol_for_identifier_reference(program_id, identifier) else {
            return base_type;
        };
        let node = NodeRef::new(program_id, identifier.node_id());
        let property_name = member.property.name.as_str();

        self.branch_effects(node)
            .into_iter()
            .find(|effect| {
                let Some(condition) = self.branch_effect_condition(program_id, *effect) else {
                    return false;
                };
                effect.assume_true
                    && self.optional_chain_property_matches_symbol(
                        program_id,
                        symbol,
                        property_name,
                        condition,
                    )
                    && !self.intervening_write_invalidates(
                        node,
                        symbol,
                        *effect,
                        condition.span(),
                        base_type,
                    )
            })
            .map_or(base_type, |_| self.narrow_by_truthiness(base_type, true))
    }

    fn branch_effect_condition(
        &self,
        program_id: ProgramId,
        effect: BranchEffect,
    ) -> Option<&'a Expression<'a>> {
        match self.nodes(program_id).kind(effect.controller) {
            AstKind::IfStatement(if_statement) => Some(&if_statement.test),
            AstKind::ConditionalExpression(conditional) => Some(&conditional.test),
            AstKind::LogicalExpression(logical) => Some(&logical.left),
            _ => None,
        }
    }

    /// Narrow a type based on one condition expression and an assumed condition outcome.
    fn narrow_by_condition(
        &self,
        node: NodeRef,
        symbol: SymbolRef,
        current_type: Ty<'a>,
        condition: &'a Expression<'a>,
        assume_true: bool,
    ) -> Ty<'a> {
        let condition = skip_parentheses(condition);

        if self.expression_matches_symbol(node.program_id, symbol, condition) {
            return self.narrow_by_truthiness(current_type, assume_true);
        }

        if assume_true
            && self.optional_chain_base_matches_symbol(node.program_id, symbol, condition)
        {
            return self.narrow_by_truthiness(current_type, true);
        }

        if let Expression::LogicalExpression(logical) = condition {
            return self.narrow_by_logical_condition(
                node,
                symbol,
                current_type,
                logical,
                assume_true,
            );
        }

        if let Expression::CallExpression(call) = condition {
            return self.narrow_by_call_type_predicate(
                node,
                symbol,
                current_type,
                call,
                assume_true,
            );
        }

        let Expression::BinaryExpression(binary) = condition else {
            return current_type;
        };

        if let Some((kind, mut effective_true)) =
            self.nullish_equality_guard(node.program_id, symbol, binary)
        {
            effective_true = effective_true == assume_true;
            return self.narrow_by_nullish_equality(node, current_type, kind, effective_true);
        }

        if let Some((target, property_name, mut effective_true)) = in_guard(binary) {
            effective_true = effective_true == assume_true;
            if !self.expression_matches_symbol(node.program_id, symbol, target) {
                return current_type;
            }
            return self.narrow_by_in_property(
                node.program_id,
                current_type,
                property_name,
                effective_true,
            );
        }

        let Some((target, witness, mut effective_true)) = typeof_guard(binary) else {
            return current_type;
        };
        effective_true = effective_true == assume_true;

        if !self.expression_matches_symbol(node.program_id, symbol, target) {
            return current_type;
        }

        let type_to_narrow = self
            .get_type_parameter_constraint(node.program_id, node.node_id, current_type)
            .unwrap_or(current_type);
        self.narrow_by_typeof(node.program_id, type_to_narrow, witness, effective_true)
    }

    fn optional_chain_base_matches_symbol(
        &self,
        program_id: ProgramId,
        symbol: SymbolRef,
        expression: &Expression<'_>,
    ) -> bool {
        let Expression::ChainExpression(chain) = skip_parentheses(expression) else {
            return false;
        };
        let object = match &chain.expression {
            ChainElement::StaticMemberExpression(member) => &member.object,
            ChainElement::ComputedMemberExpression(member) => &member.object,
            _ => return false,
        };
        self.expression_matches_symbol(program_id, symbol, object)
    }

    fn optional_chain_property_matches_symbol(
        &self,
        program_id: ProgramId,
        symbol: SymbolRef,
        property_name: &str,
        expression: &Expression<'_>,
    ) -> bool {
        let Expression::ChainExpression(chain) = skip_parentheses(expression) else {
            return false;
        };
        let ChainElement::StaticMemberExpression(member) = &chain.expression else {
            return false;
        };
        member.property.name == property_name
            && self.expression_matches_symbol(program_id, symbol, &member.object)
    }

    fn narrow_by_logical_condition(
        &self,
        node: NodeRef,
        symbol: SymbolRef,
        current_type: Ty<'a>,
        logical: &'a LogicalExpression<'a>,
        assume_true: bool,
    ) -> Ty<'a> {
        match (logical.operator, assume_true) {
            (LogicalOperator::And, true) => {
                let left_type =
                    self.narrow_by_condition(node, symbol, current_type, &logical.left, true);
                self.narrow_by_condition(node, symbol, left_type, &logical.right, true)
            }
            (LogicalOperator::Or, false) => {
                let left_type =
                    self.narrow_by_condition(node, symbol, current_type, &logical.left, false);
                self.narrow_by_condition(node, symbol, left_type, &logical.right, false)
            }
            _ => current_type,
        }
    }

    fn narrow_by_call_type_predicate(
        &self,
        node: NodeRef,
        symbol: SymbolRef,
        current_type: Ty<'a>,
        call: &'a oxc_ast::ast::CallExpression<'a>,
        assume_true: bool,
    ) -> Ty<'a> {
        if !assume_true {
            return current_type;
        }

        let Some(predicate) = self.get_type_predicate_of_call_expression(node.program_id, call)
        else {
            return current_type;
        };
        let (parameter_index, target_type) = match predicate {
            TyTypePredicate::Identifier {
                parameter_index,
                target_type,
                ..
            } => (parameter_index, Some(target_type)),
            TyTypePredicate::AssertsIdentifier {
                parameter_index,
                target_type,
                ..
            } => (parameter_index, target_type),
            TyTypePredicate::This { .. } | TyTypePredicate::AssertsThis { .. } => {
                return current_type;
            }
        };
        let (Some(parameter_index), Some(target_type)) = (parameter_index, target_type) else {
            return current_type;
        };
        let Some(argument) = call
            .arguments
            .get(parameter_index)
            .and_then(|argument| argument.as_expression())
        else {
            return current_type;
        };
        if !self.expression_matches_symbol(node.program_id, symbol, argument) {
            return current_type;
        }

        self.with_implicit_type_arguments_visible(target_type)
    }
}

#[derive(Clone, Copy)]
enum NullishEqualityKind {
    Null,
    Undefined,
}

impl NullishEqualityKind {
    fn matches(self, ty: Ty<'_>) -> bool {
        match self {
            Self::Null => matches!(ty, Ty::Null),
            Self::Undefined => matches!(ty, Ty::Undefined | Ty::Void),
        }
    }
}

impl<'a> Checker<'a, '_> {
    fn other_nullish_type(&self, kind: NullishEqualityKind) -> Ty<'a> {
        match kind {
            NullishEqualityKind::Null => self.ty.undefined(),
            NullishEqualityKind::Undefined => self.ty.null(),
        }
    }

    fn nullish_equality_guard(
        &self,
        program_id: ProgramId,
        symbol: SymbolRef,
        binary: &oxc_ast::ast::BinaryExpression<'_>,
    ) -> Option<(NullishEqualityKind, bool)> {
        let equality = match binary.operator {
            BinaryOperator::Equality | BinaryOperator::StrictEquality => true,
            BinaryOperator::Inequality | BinaryOperator::StrictInequality => false,
            _ => return None,
        };

        let left = skip_parentheses(&binary.left);
        let right = skip_parentheses(&binary.right);
        let nullish_kind = |expression: &Expression<'_>| {
            if self.is_global_undefined_expression(program_id, expression) {
                Some(NullishEqualityKind::Undefined)
            } else if matches!(expression, Expression::NullLiteral(_)) {
                Some(NullishEqualityKind::Null)
            } else {
                None
            }
        };
        if self.expression_matches_symbol(program_id, symbol, left) {
            nullish_kind(right).map(|kind| (kind, equality))
        } else if self.expression_matches_symbol(program_id, symbol, right) {
            nullish_kind(left).map(|kind| (kind, equality))
        } else {
            None
        }
    }

    fn narrow_by_nullish_equality(
        &self,
        node: NodeRef,
        ty: Ty<'a>,
        kind: NullishEqualityKind,
        assume_nullish: bool,
    ) -> Ty<'a> {
        if ty.is_any_like(self.arena()) || ty.is_unknown() {
            return ty;
        }
        if assume_nullish {
            return self.filter_type(ty, |ty| kind.matches(ty));
        }
        self.remove_nullish_from_type(node, ty, kind)
    }
}

fn in_guard<'a>(
    binary: &'a oxc_ast::ast::BinaryExpression<'a>,
) -> Option<(&'a Expression<'a>, &'a str, bool)> {
    if binary.operator != BinaryOperator::In {
        return None;
    }
    let property_name = string_literal_value(skip_parentheses(&binary.left))?;
    Some((skip_parentheses(&binary.right), property_name, true))
}

impl<'a> Checker<'a, '_> {
    fn narrow_by_in_property(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        property_name: &'a str,
        assume_true: bool,
    ) -> Ty<'a> {
        if !assume_true || ty.is_any_like(self.arena()) {
            return ty;
        }

        let property_key = self.ty.string_literal(property_name);
        let property_record =
            self.get_global_record_type(program_id, property_key, self.ty.unknown());
        match self.ty_kind(ty) {
            TyKind::Unknown => property_record,
            TyKind::PrimitiveObject
            | TyKind::Function(_)
            | TyKind::TypeReference(_)
            | TyKind::Object(_) => self.ty.intersection([ty, property_record]),
            _ => ty,
        }
    }

    fn remove_nullish_from_type(
        &self,
        node: NodeRef,
        ty: Ty<'a>,
        kind: NullishEqualityKind,
    ) -> Ty<'a> {
        if !matches!(self.ty_kind(ty), TyKind::Union(_)) {
            return self
                .non_nullish_constituent(node, ty, kind)
                .unwrap_or_else(|| self.ty.never());
        }
        ty.map_union(self.arena(), |ty| {
            self.non_nullish_constituent(node, ty, kind)
        })
    }

    fn non_nullish_constituent(
        &self,
        node: NodeRef,
        ty: Ty<'a>,
        kind: NullishEqualityKind,
    ) -> Option<Ty<'a>> {
        if kind.matches(ty) {
            None
        } else if self.is_scoped_type_parameter_reference(node.program_id, node.node_id, ty) {
            Some(
                self.ty.intersection([
                    ty,
                    self.arena()
                        .union([self.ty.object([]), self.other_nullish_type(kind)]),
                ]),
            )
        } else {
            Some(ty)
        }
    }
}

/// Recognize `typeof x === "kind"` and reversed-operand equivalents.
fn typeof_guard<'a>(
    binary: &'a oxc_ast::ast::BinaryExpression<'a>,
) -> Option<(&'a Expression<'a>, TypeofWitness, bool)> {
    let equality = match binary.operator {
        BinaryOperator::Equality | BinaryOperator::StrictEquality => true,
        BinaryOperator::Inequality | BinaryOperator::StrictInequality => false,
        _ => return None,
    };

    typeof_guard_operands(&binary.left, &binary.right)
        .or_else(|| typeof_guard_operands(&binary.right, &binary.left))
        .map(|(target, witness)| (target, witness, equality))
}

/// Recognize one operand ordering for a `typeof` guard.
fn typeof_guard_operands<'a>(
    typeof_operand: &'a Expression<'a>,
    witness_operand: &'a Expression<'a>,
) -> Option<(&'a Expression<'a>, TypeofWitness)> {
    let target = typeof_target(skip_parentheses(typeof_operand))?;
    let witness =
        TypeofWitness::from_literal(string_literal_value(skip_parentheses(witness_operand))?)?;
    Some((target, witness))
}

/// Return the operand of a `typeof` expression.
fn typeof_target<'a>(expression: &'a Expression<'a>) -> Option<&'a Expression<'a>> {
    let Expression::UnaryExpression(unary) = expression else {
        return None;
    };
    (unary.operator == UnaryOperator::Typeof).then(|| skip_parentheses(&unary.argument))
}

/// Return the text value of a string-literal expression.
fn string_literal_value<'a>(expression: &'a Expression<'a>) -> Option<&'a str> {
    let Expression::StringLiteral(literal) = expression else {
        return None;
    };
    Some(literal.value.as_str())
}

/// Peel parenthesized expressions without changing the semantic reference being checked.
fn skip_parentheses<'a>(expression: &'a Expression<'a>) -> &'a Expression<'a> {
    match expression {
        Expression::ParenthesizedExpression(parenthesized) => {
            skip_parentheses(&parenthesized.expression)
        }
        _ => expression,
    }
}

/// Check whether an expression is an identifier reference to the target symbol.
impl<'a> Checker<'a, '_> {
    fn expression_matches_symbol(
        &self,
        program_id: ProgramId,
        symbol: SymbolRef,
        expression: &Expression<'_>,
    ) -> bool {
        if symbol.program_id != program_id {
            return false;
        }

        let expression = skip_parentheses(expression);
        let Expression::Identifier(identifier) = expression else {
            return false;
        };

        self.symbol_for_identifier_reference(program_id, identifier) == Some(symbol)
    }

    /// Apply the currently supported true-branch truthiness facts.
    fn narrow_by_truthiness(&self, ty: Ty<'a>, assume_true: bool) -> Ty<'a> {
        if !assume_true || ty.is_any_like(self.arena()) || ty.is_unknown() {
            return ty;
        }

        self.filter_type(ty, |ty| !self.is_definitely_falsy(ty))
    }

    /// Apply a `typeof` witness or its negation to a type.
    fn narrow_by_typeof(
        &self,
        program_id: ProgramId,
        ty: Ty<'a>,
        witness: TypeofWitness,
        assume_true: bool,
    ) -> Ty<'a> {
        if ty.is_any_like(self.arena()) {
            return ty;
        }

        if matches!(ty, Ty::Unknown) {
            return if assume_true {
                match witness {
                    TypeofWitness::String => self.ty.string(),
                    TypeofWitness::Number => self.ty.number(),
                    TypeofWitness::Boolean => self.ty.boolean(),
                    TypeofWitness::Bigint => self.ty.bigint(),
                    TypeofWitness::Undefined => self.ty.undefined(),
                    TypeofWitness::Object => {
                        self.ty.union([self.ty.primitive_object(), self.ty.null()])
                    }
                    TypeofWitness::Function => self.get_global_function_type(program_id),
                }
            } else {
                ty
            };
        }

        self.filter_type(ty, |ty| {
            self.type_matches_typeof(ty, witness) == assume_true
        })
    }

    /// Filter a type, distributing over union constituents and reducing the result.
    fn filter_type(&self, ty: Ty<'a>, keep: impl Fn(Ty<'a>) -> bool + Copy) -> Ty<'a> {
        if !matches!(self.ty_kind(ty), TyKind::Union(_)) {
            return if keep(ty) { ty } else { self.ty.never() };
        }
        ty.map_union(self.arena(), |ty| keep(ty).then_some(ty))
    }

    /// Return whether a type is definitely in the runtime domain named by a `typeof` witness.
    fn type_matches_typeof(&self, ty: Ty<'a>, witness: TypeofWitness) -> bool {
        let data = self.ty_kind(ty);
        match witness {
            TypeofWitness::String => ty.is_string_like(self.arena()),
            TypeofWitness::Number => {
                matches!(data, TyKind::Number | TyKind::NumberLiteral(_))
            }
            TypeofWitness::Boolean => {
                matches!(data, TyKind::Boolean | TyKind::BooleanLiteral(_))
            }
            TypeofWitness::Bigint => {
                matches!(data, TyKind::Bigint | TyKind::BigIntLiteral(_))
            }
            TypeofWitness::Undefined => matches!(data, TyKind::Undefined | TyKind::Void),
            TypeofWitness::Object => matches!(
                data,
                TyKind::Null
                    | TyKind::PrimitiveObject
                    | TyKind::Object(_)
                    | TyKind::ModuleNamespace(_)
                    | TyKind::Array(_)
                    | TyKind::Tuple(_)
                    | TyKind::TypeReference(_)
            ),
            TypeofWitness::Function => matches!(data, TyKind::Function(_)),
        }
    }

    /// Return whether a constituent is currently known to be removed by a truthy check.
    fn is_definitely_falsy(&self, ty: Ty<'a>) -> bool {
        match self.ty_kind(ty) {
            TyKind::Undefined | TyKind::Null => true,
            TyKind::BooleanLiteral(value) => !value,
            _ => false,
        }
    }

    /// Return whether an intervening write may escape the candidate narrowed type.
    fn intervening_write_invalidates(
        &self,
        node: NodeRef,
        symbol: SymbolRef,
        effect: BranchEffect,
        condition_span: Span,
        candidate_type: Ty<'a>,
    ) -> bool {
        if symbol.program_id != node.program_id {
            return false;
        }

        let query_span = self.node_kind(node).span();
        let branch_span = self.nodes(node.program_id).kind(effect.branch_root).span();
        let cfg = self.cfg(symbol.program_id);
        let branch_block = self.cfg_id_in_program(symbol.program_id, effect.branch_root);
        let query_block = self.cfg_id(node);

        self.symbol_writes(symbol.program_id, symbol.symbol_id)
            .into_iter()
            .filter(|write| {
                write.span.start > condition_span.end
                    && write.span.end <= query_span.start
                    && branch_span.contains_inclusive(write.span)
                    && cfg.is_reachable(branch_block, write.block_id)
                    && cfg.is_reachable(write.block_id, query_block)
            })
            .any(|write| {
                self.assigned_type_for_write(symbol.program_id, write.node_id)
                    .is_none_or(|assigned| !self.is_assignable_to(assigned, candidate_type))
            })
    }

    fn assigned_type_for_write(
        &self,
        program_id: ProgramId,
        write_node_id: oxc_semantic::NodeId,
    ) -> Option<Ty<'a>> {
        if let AstKind::VariableDeclarator(declarator) = self.nodes(program_id).kind(write_node_id)
        {
            return declarator.init.as_ref().map(|initializer| {
                let is_const = matches!(
                    self.nodes(program_id).parent_kind(write_node_id),
                    AstKind::VariableDeclaration(declaration)
                        if declaration.kind.is_const()
                );
                let flags = if is_const {
                    CheckMode::CONTEXT_FREE | CheckMode::PRESERVE_LITERALS
                } else {
                    CheckMode::CONTEXT_FREE
                };
                self.get_type_of_expression_with_node(
                    program_id,
                    initializer,
                    Some(write_node_id),
                    flags,
                )
            });
        }
        let assignment_id = self.nodes(program_id).parent_id(write_node_id);
        let AstKind::AssignmentExpression(assignment) = self.nodes(program_id).kind(assignment_id)
        else {
            return None;
        };
        if assignment.operator != oxc_syntax::operator::AssignmentOperator::Assign
            || assignment.left.span() != self.nodes(program_id).kind(write_node_id).span()
        {
            return None;
        }
        Some(self.get_type_of_expression_with_node(
            program_id,
            &assignment.right,
            Some(assignment_id),
            CheckMode::CONTEXT_FREE,
        ))
    }

    fn assignment_flow_type(
        &self,
        node: NodeRef,
        symbol: SymbolRef,
        current_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        let nodes = self.nodes(node.program_id);
        if self.is_for_in_expression_reference(node, symbol) {
            return None;
        }
        if self.is_in_self_referential_sequence_assignment(node, symbol) {
            return None;
        }
        let mut is_compound_write = false;
        if let AstKind::IdentifierReference(identifier) = nodes.kind(node.node_id)
            && identifier.reference_id.get().is_some_and(|reference_id| {
                self.semantic(node.program_id)
                    .scoping()
                    .get_reference(reference_id)
                    .is_write()
            })
        {
            let parent_id = nodes.parent_id(node.node_id);
            let AstKind::AssignmentExpression(assignment) = nodes.kind(parent_id) else {
                return None;
            };
            if assignment.operator == AssignmentOperator::Assign {
                return None;
            }
            is_compound_write = true;
        }
        let assignment_flow = self.assignment_flow(node, symbol.symbol_id)?;
        if is_compound_write && !assignment_flow.crosses_blocks {
            return None;
        }
        if !current_type.is_any_like(self.arena()) && !current_type.is_union(self.arena()) {
            return None;
        }
        let seed_type =
            self.assigned_type_for_write(symbol.program_id, assignment_flow.seed.node_id)?;
        if !self.is_assignable_to(seed_type, current_type) {
            return None;
        }
        if current_type.array_element_type(self.arena()).is_some()
            && seed_type.array_element_type(self.arena()).is_some()
        {
            return Some(current_type);
        }
        if assignment_flow.loop_writes.is_empty() {
            return Some(seed_type);
        }

        let mut types = UnionAccumulator::new(self.arena());
        types.add(seed_type);
        for write in assignment_flow.loop_writes {
            types.add(self.loop_write_type(symbol.program_id, write.node_id, seed_type)?);
        }
        Some(types.build())
    }

    fn is_for_in_expression_reference(&self, node: NodeRef, symbol: SymbolRef) -> bool {
        self.nodes(node.program_id)
            .ancestors(node.node_id)
            .find_map(|ancestor| match ancestor.kind() {
                AstKind::ForInStatement(statement) => Some(
                    statement
                        .right
                        .span()
                        .contains_inclusive(self.node_kind(node).span())
                        || statement
                            .body
                            .span()
                            .contains_inclusive(self.node_kind(node).span()),
                ),
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) => Some(false),
                _ => None,
            })
            .unwrap_or(false)
            && symbol.program_id == node.program_id
    }

    fn is_in_self_referential_sequence_assignment(&self, node: NodeRef, symbol: SymbolRef) -> bool {
        let nodes = self.nodes(node.program_id);
        let mut inside_sequence = false;
        for ancestor in nodes.ancestors(node.node_id) {
            match ancestor.kind() {
                AstKind::SequenceExpression(_) => inside_sequence = true,
                AstKind::AssignmentExpression(assignment) if inside_sequence => {
                    let Some(SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier)) =
                        assignment.left.as_simple_assignment_target()
                    else {
                        continue;
                    };
                    if self.symbol_for_identifier_reference(node.program_id, identifier)
                        == Some(symbol)
                    {
                        return true;
                    }
                }
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) => return false,
                _ => {}
            }
        }
        false
    }

    fn loop_write_type(
        &self,
        program_id: ProgramId,
        write_node_id: oxc_semantic::NodeId,
        seed_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        if let Some(assigned) = self.assigned_type_for_write(program_id, write_node_id) {
            return Some(assigned);
        }

        let nodes = self.nodes(program_id);
        let parent_id = nodes.parent_id(write_node_id);
        match nodes.kind(parent_id) {
            AstKind::AssignmentExpression(assignment)
                if assignment.left.span() == nodes.kind(write_node_id).span() =>
            {
                match assignment.operator {
                    AssignmentOperator::Addition => {
                        let right = self.get_type_of_expression_with_node(
                            program_id,
                            &assignment.right,
                            Some(parent_id),
                            CheckMode::CONTEXT_FREE,
                        );
                        if self.is_assignable_to(seed_type, self.ty.number())
                            && self.is_assignable_to(right, self.ty.number())
                        {
                            Some(self.ty.number())
                        } else {
                            None
                        }
                    }
                    AssignmentOperator::Subtraction
                    | AssignmentOperator::Multiplication
                    | AssignmentOperator::Division
                    | AssignmentOperator::Remainder
                    | AssignmentOperator::Exponential
                    | AssignmentOperator::ShiftLeft
                    | AssignmentOperator::ShiftRight
                    | AssignmentOperator::ShiftRightZeroFill
                    | AssignmentOperator::BitwiseOR
                    | AssignmentOperator::BitwiseXOR
                    | AssignmentOperator::BitwiseAnd => Some(self.ty.number()),
                    _ => None,
                }
            }
            AstKind::UpdateExpression(_) => Some(self.ty.number()),
            _ => None,
        }
    }
}
