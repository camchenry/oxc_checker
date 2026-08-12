use std::collections::HashMap;

use oxc_ast::{
    AstKind,
    ast::{Argument, ArrayExpression, Expression},
};
use oxc_semantic::NodeId;
use oxc_span::GetSpan;
use oxc_syntax::operator::AssignmentOperator;

use crate::{
    checker::{CheckerReturn, NodeRef, SymbolRef},
    checker_impl::GetTypeFlags,
    program::{self, ProgramId},
    types::{TupleElement, Ty, TypeData},
};

enum EvolvingArrayEvent<'a> {
    Add(Ty<'a>),
    Reset(Ty<'a>),
}

/// Return the element type for an empty array literal in expression typing.
///
/// TypeScript-Go models direct empty-array local initializers as evolving arrays.
/// Since evolving arrays do not escape ordinary expression typing, the initializer
/// record still displays as `any[]` while nested empty array expressions remain
/// `never[]`.
pub(crate) fn empty_array_literal_element_type<'a>(
    checker: &CheckerReturn<'a, '_>,
    program_id: ProgramId,
    array_expression: &'a ArrayExpression<'a>,
    node_id: Option<NodeId>,
) -> Ty<'a> {
    if is_direct_empty_array_variable_initializer(checker, program_id, array_expression, node_id) {
        Ty::any()
    } else {
        Ty::never()
    }
}

/// Return the finalized flow type for a reference to an evolving empty-array local.
pub(crate) fn get_flow_type_of_reference<'a>(
    checker: &CheckerReturn<'a, '_>,
    node: NodeRef,
    symbol: SymbolRef,
    base_type: Ty<'a>,
) -> Option<Ty<'a>> {
    let (_declaration_id, declarator) = checker.variable_declarator_for_symbol(symbol)?;
    if declarator.type_annotation.is_some()
        || !declarator
            .init
            .as_ref()
            .is_some_and(|init| expression_is_empty_array_literal(init))
    {
        return None;
    }

    let query_span = checker.node_kind(node).span();
    let declaration_span = declarator.span;
    if query_span.start <= declaration_span.start {
        return None;
    }

    if let Some(flow_type) = checker
        .evolving_array_flow_cache
        .borrow()
        .get(&symbol)
        .and_then(|flow_types| flow_types.get(&node.node_id))
        .copied()
    {
        return Some(flow_type);
    }

    let flow_types = build_flow_type_cache(checker, symbol, declaration_span, base_type);
    let flow_type = flow_types.get(&node.node_id).copied();
    checker
        .evolving_array_flow_cache
        .borrow_mut()
        .insert(symbol, flow_types);
    flow_type
}

fn build_flow_type_cache<'a>(
    checker: &CheckerReturn<'a, '_>,
    symbol: SymbolRef,
    declaration_span: oxc_span::Span,
    base_type: Ty<'a>,
) -> HashMap<NodeId, Ty<'a>> {
    let mut references = checker
        .semantic(symbol.program_id)
        .symbol_references(symbol.symbol_id)
        .filter_map(|reference| {
            let reference_id = reference.node_id();
            let reference_span = checker.nodes(symbol.program_id).kind(reference_id).span();
            if reference_span.start <= declaration_span.start {
                return None;
            }
            Some((
                reference_span.start,
                reference_id,
                evolving_array_event_for_reference(checker, symbol.program_id, reference_id),
            ))
        })
        .collect::<Vec<_>>();
    references.sort_by_key(|(start, _, _)| *start);

    let mut flow_types = HashMap::with_capacity(references.len());
    let mut element_types = Vec::new();
    let empty_element_type = finalized_empty_element_type(checker, base_type);
    let mut flow_type = Ty::array(checker.arena(), empty_element_type);

    for (_, reference_id, event) in references {
        flow_types.insert(reference_id, flow_type);

        match event {
            Some(EvolvingArrayEvent::Add(ty)) => {
                if !element_types
                    .iter()
                    .any(|existing| checker.arena().is_type_identical_to(*existing, ty))
                {
                    element_types.push(ty);
                    flow_type =
                        array_type_from_elements(checker, &element_types, empty_element_type);
                }
            }
            Some(EvolvingArrayEvent::Reset(ty)) => {
                element_types.clear();
                if !matches!(ty, Ty::Never) {
                    element_types.push(ty);
                }
                flow_type = array_type_from_elements(checker, &element_types, empty_element_type);
            }
            None => {}
        }
    }

    flow_types
}

fn array_type_from_elements<'a>(
    checker: &CheckerReturn<'a, '_>,
    element_types: &[Ty<'a>],
    empty_element_type: Ty<'a>,
) -> Ty<'a> {
    Ty::array(
        checker.arena(),
        match element_types {
            [] => empty_element_type,
            [ty] => *ty,
            types => Ty::union(checker.arena(), types.iter().copied()),
        },
    )
}

fn is_direct_empty_array_variable_initializer<'a>(
    checker: &CheckerReturn<'a, '_>,
    program_id: ProgramId,
    array_expression: &'a ArrayExpression<'a>,
    node_id: Option<NodeId>,
) -> bool {
    let Some(node_id) = node_id else {
        return false;
    };
    let AstKind::VariableDeclarator(declarator) =
        checker.node_kind(NodeRef::new(program_id, node_id))
    else {
        return false;
    };
    declarator
        .init
        .as_ref()
        .is_some_and(|init| init.span() == array_expression.span)
}

fn expression_is_empty_array_literal(expression: &Expression<'_>) -> bool {
    matches!(expression, Expression::ArrayExpression(array) if array.elements.is_empty())
}

fn evolving_array_event_for_reference<'a>(
    checker: &CheckerReturn<'a, '_>,
    program_id: ProgramId,
    reference_id: NodeId,
) -> Option<EvolvingArrayEvent<'a>> {
    push_call_element_events(checker, program_id, reference_id)
        .or_else(|| indexed_assignment_element_event(checker, program_id, reference_id))
        .or_else(|| direct_assignment_event(checker, program_id, reference_id))
}

fn push_call_element_events<'a>(
    checker: &CheckerReturn<'a, '_>,
    program_id: ProgramId,
    reference_id: NodeId,
) -> Option<EvolvingArrayEvent<'a>> {
    let member_id = checker.nodes(program_id).parent_id(reference_id);
    let AstKind::StaticMemberExpression(member) = checker.nodes(program_id).kind(member_id) else {
        return None;
    };
    if !matches!(member.property.name.as_str(), "push" | "unshift") {
        return None;
    }
    if member.object.span() != checker.nodes(program_id).kind(reference_id).span() {
        return None;
    }

    let call_id = checker.nodes(program_id).parent_id(member_id);
    let AstKind::CallExpression(call) = checker.nodes(program_id).kind(call_id) else {
        return None;
    };
    if call.callee.span() != member.span {
        return None;
    }

    let element_types = call
        .arguments
        .iter()
        .filter_map(|argument| argument_expression(argument))
        .map(|argument| {
            checker.get_type_of_expression_with_node(
                program_id,
                argument,
                Some(call_id),
                GetTypeFlags::NONE,
            )
        })
        .collect::<Vec<_>>();
    if element_types.is_empty() {
        return None;
    }
    Some(EvolvingArrayEvent::Add(match element_types.as_slice() {
        [ty] => *ty,
        _ => Ty::union(checker.arena(), element_types),
    }))
}

fn indexed_assignment_element_event<'a>(
    checker: &CheckerReturn<'a, '_>,
    program_id: ProgramId,
    reference_id: NodeId,
) -> Option<EvolvingArrayEvent<'a>> {
    let member_id = checker.nodes(program_id).parent_id(reference_id);
    let AstKind::ComputedMemberExpression(member) = checker.nodes(program_id).kind(member_id)
    else {
        return None;
    };
    if member.object.span() != checker.nodes(program_id).kind(reference_id).span() {
        return None;
    }

    let assignment_id = checker.nodes(program_id).parent_id(member_id);
    let AstKind::AssignmentExpression(assignment) = checker.nodes(program_id).kind(assignment_id)
    else {
        return None;
    };
    if assignment.operator != AssignmentOperator::Assign || assignment.left.span() != member.span {
        return None;
    }

    Some(EvolvingArrayEvent::Add(
        checker.get_type_of_expression_with_node(
            program_id,
            &assignment.right,
            Some(assignment_id),
            GetTypeFlags::CONTEXT_FREE,
        ),
    ))
}

fn direct_assignment_event<'a>(
    checker: &CheckerReturn<'a, '_>,
    program_id: ProgramId,
    reference_id: NodeId,
) -> Option<EvolvingArrayEvent<'a>> {
    let assignment_id = checker.nodes(program_id).parent_id(reference_id);
    let AstKind::AssignmentExpression(assignment) = checker.nodes(program_id).kind(assignment_id)
    else {
        return None;
    };
    if assignment.operator != AssignmentOperator::Assign
        || assignment.left.span() != checker.nodes(program_id).kind(reference_id).span()
    {
        return None;
    }

    let assigned_type = checker.get_type_of_expression_with_node(
        program_id,
        &assignment.right,
        Some(assignment_id),
        GetTypeFlags::CONTEXT_FREE,
    );

    match checker.arena().type_data(assigned_type) {
        TypeData::Array(array) => Some(EvolvingArrayEvent::Reset(array.element_type)),
        TypeData::Tuple(tuple) => Some(EvolvingArrayEvent::Reset(Ty::union(
            checker.arena(),
            tuple.elements.iter().map(|element| match element {
                TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => {
                    *ty
                }
            }),
        ))),
        _ => None,
    }
}

fn argument_expression<'a>(argument: &'a Argument<'a>) -> Option<&'a Expression<'a>> {
    argument.as_expression()
}

fn finalized_empty_element_type<'a>(checker: &CheckerReturn<'a, '_>, base_type: Ty<'a>) -> Ty<'a> {
    match checker.arena().type_data(base_type) {
        TypeData::Array(array) if array.element_type.is_never() => Ty::any(),
        TypeData::Array(array) => array.element_type,
        _ => Ty::any(),
    }
}
