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
    program,
    types::{TupleElement, Ty},
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
    program_id: program::ProgramId,
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

    let mut events = checker
        .semantic(symbol.program_id)
        .symbol_references(symbol.symbol_id)
        .filter_map(|reference| {
            let reference_id = reference.node_id();
            let reference_span = checker.nodes(symbol.program_id).kind(reference_id).span();
            if reference_span.start <= declaration_span.start
                || reference_span.start >= query_span.start
            {
                return None;
            }
            evolving_array_event_for_reference(checker, symbol.program_id, reference_id)
                .map(|event| (reference_span.start, event))
        })
        .collect::<Vec<_>>();
    events.sort_by_key(|(start, _)| *start);

    let mut element_types = Vec::new();
    for (_, event) in events {
        match event {
            EvolvingArrayEvent::Add(ty) => {
                if !element_types.contains(&ty) {
                    element_types.push(ty);
                }
            }
            EvolvingArrayEvent::Reset(ty) => {
                element_types.clear();
                if !matches!(ty, Ty::Never) {
                    element_types.push(ty);
                }
            }
        }
    }

    Some(Ty::array(
        checker.arena(),
        if element_types.is_empty() {
            finalized_empty_element_type(base_type)
        } else if element_types.len() == 1 {
            element_types[0]
        } else {
            Ty::union(checker.arena(), element_types)
        },
    ))
}

fn is_direct_empty_array_variable_initializer<'a>(
    checker: &CheckerReturn<'a, '_>,
    program_id: program::ProgramId,
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
    program_id: program::ProgramId,
    reference_id: NodeId,
) -> Option<EvolvingArrayEvent<'a>> {
    push_call_element_events(checker, program_id, reference_id)
        .or_else(|| indexed_assignment_element_event(checker, program_id, reference_id))
        .or_else(|| direct_assignment_event(checker, program_id, reference_id))
}

fn push_call_element_events<'a>(
    checker: &CheckerReturn<'a, '_>,
    program_id: program::ProgramId,
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
    program_id: program::ProgramId,
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
    program_id: program::ProgramId,
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

    match assigned_type {
        Ty::Array(array) => Some(EvolvingArrayEvent::Reset(array.element_type)),
        Ty::Tuple(tuple) => Some(EvolvingArrayEvent::Reset(Ty::union(
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

fn finalized_empty_element_type(base_type: Ty<'_>) -> Ty<'_> {
    match base_type {
        Ty::Array(array) if array.element_type.is_never() => Ty::any(),
        Ty::Array(array) => array.element_type,
        _ => Ty::any(),
    }
}
