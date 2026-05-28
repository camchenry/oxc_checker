use oxc_ast::{
    AstKind,
    ast::{Expression, IfStatement},
};
use oxc_semantic::NodeId;
use oxc_span::{GetSpan, Span};
use oxc_syntax::operator::{BinaryOperator, UnaryOperator};

use crate::{CheckerReturn, NodeRef, SymbolRef, types::Ty};

/// A branch-local condition that may narrow identifier references inside an `if` arm.
#[derive(Clone, Copy)]
struct BranchFact<'a> {
    condition: &'a Expression<'a>,
    condition_span: Span,
    branch_span: Span,
    assume_true: bool,
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
pub(crate) fn get_flow_type_of_reference<'a>(
    checker: &CheckerReturn<'a, '_>,
    node: NodeRef,
    symbol: SymbolRef,
    base_type: Ty<'a>,
) -> Ty<'a> {
    if checker.semantic(node.program_id).cfg().is_none() {
        return base_type;
    }

    let mut narrowed_type = base_type;
    let mut facts = collect_branch_facts(checker, node);
    facts.reverse();

    for fact in facts {
        let candidate_type = narrow_by_condition(
            checker,
            symbol,
            narrowed_type,
            fact.condition,
            fact.assume_true,
        );
        if candidate_type == narrowed_type {
            continue;
        }
        if has_intervening_write(checker, node, symbol, fact) {
            continue;
        }
        narrowed_type = candidate_type;
    }

    narrowed_type
}

/// Collect enclosing `if` branch facts for a reference location, innermost first.
fn collect_branch_facts<'a>(checker: &CheckerReturn<'a, '_>, node: NodeRef) -> Vec<BranchFact<'a>> {
    let query_span = checker.node_kind(node).span();
    let mut facts = Vec::new();

    for (_ancestor_id, ancestor) in checker
        .nodes(node.program_id)
        .ancestors_enumerated(node.node_id)
    {
        match ancestor.kind() {
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Class(_) => break,
            AstKind::IfStatement(if_statement) => {
                if let Some(fact) = branch_fact_for_if(if_statement, query_span) {
                    facts.push(fact);
                }
            }
            _ => {}
        }
    }

    facts
}

/// Return the branch fact for an `if` statement when a query is inside one of its arms.
fn branch_fact_for_if<'a>(
    if_statement: &'a IfStatement<'a>,
    query_span: Span,
) -> Option<BranchFact<'a>> {
    let condition = &if_statement.test;
    let condition_span = condition.span();
    let consequent_span = if_statement.consequent.span();
    if consequent_span.contains_inclusive(query_span) {
        return Some(BranchFact {
            condition,
            condition_span,
            branch_span: consequent_span,
            assume_true: true,
        });
    }

    let alternate = if_statement.alternate.as_ref()?;
    let alternate_span = alternate.span();
    if alternate_span.contains_inclusive(query_span) {
        return Some(BranchFact {
            condition,
            condition_span,
            branch_span: alternate_span,
            assume_true: false,
        });
    }

    None
}

/// Narrow a type based on one condition expression and an assumed condition outcome.
fn narrow_by_condition<'a>(
    checker: &CheckerReturn<'a, '_>,
    symbol: SymbolRef,
    current_type: Ty<'a>,
    condition: &'a Expression<'a>,
    assume_true: bool,
) -> Ty<'a> {
    let condition = skip_parentheses(condition);

    if expression_matches_symbol(checker, symbol, condition) {
        return narrow_by_truthiness(checker, current_type, assume_true);
    }

    let Expression::BinaryExpression(binary) = condition else {
        return current_type;
    };

    let Some((target, witness, mut effective_true)) = typeof_guard(binary) else {
        return current_type;
    };
    effective_true = effective_true == assume_true;

    if !expression_matches_symbol(checker, symbol, target) {
        return current_type;
    }

    narrow_by_typeof(checker, current_type, witness, effective_true)
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
fn expression_matches_symbol(
    checker: &CheckerReturn<'_, '_>,
    symbol: SymbolRef,
    expression: &Expression<'_>,
) -> bool {
    let expression = skip_parentheses(expression);
    let Expression::Identifier(identifier) = expression else {
        return false;
    };

    identifier.reference_id.get().and_then(|reference_id| {
        checker
            .semantic(symbol.program_id)
            .scoping()
            .get_reference(reference_id)
            .symbol_id()
    }) == Some(symbol.symbol_id)
}

/// Apply the currently supported true-branch truthiness facts.
fn narrow_by_truthiness<'a>(
    checker: &CheckerReturn<'a, '_>,
    ty: Ty<'a>,
    assume_true: bool,
) -> Ty<'a> {
    if !assume_true || matches!(ty, Ty::Any | Ty::Unknown) {
        return ty;
    }

    filter_type(checker, ty, |ty| !is_definitely_falsy(ty))
}

/// Apply a `typeof` witness or its negation to a type.
fn narrow_by_typeof<'a>(
    checker: &CheckerReturn<'a, '_>,
    ty: Ty<'a>,
    witness: TypeofWitness,
    assume_true: bool,
) -> Ty<'a> {
    if matches!(ty, Ty::Any | Ty::Unknown) {
        return ty;
    }

    filter_type(checker, ty, |ty| {
        type_matches_typeof(ty, witness) == assume_true
    })
}

/// Filter a type, distributing over union constituents and reducing the result.
fn filter_type<'a>(
    checker: &CheckerReturn<'a, '_>,
    ty: Ty<'a>,
    keep: impl Fn(Ty<'a>) -> bool + Copy,
) -> Ty<'a> {
    match ty {
        Ty::Union(union) => {
            let types = union
                .types
                .iter()
                .copied()
                .filter(|ty| keep(*ty))
                .collect::<Vec<_>>();
            if types.is_empty() {
                Ty::never()
            } else {
                Ty::union(checker.arena(), types)
            }
        }
        _ if keep(ty) => ty,
        _ => Ty::never(),
    }
}

/// Return whether a type is definitely in the runtime domain named by a `typeof` witness.
fn type_matches_typeof(ty: Ty<'_>, witness: TypeofWitness) -> bool {
    match witness {
        TypeofWitness::String => matches!(
            ty,
            Ty::String | Ty::StringLiteral(_) | Ty::TemplateLiteral(_)
        ),
        TypeofWitness::Number => matches!(ty, Ty::Number | Ty::NumberLiteral(_)),
        TypeofWitness::Boolean => matches!(ty, Ty::Boolean | Ty::BooleanLiteral(_)),
        TypeofWitness::Bigint => matches!(ty, Ty::Bigint | Ty::BigIntLiteral(_)),
        TypeofWitness::Undefined => matches!(ty, Ty::Undefined | Ty::Void),
        TypeofWitness::Object => matches!(
            ty,
            Ty::Null
                | Ty::PrimitiveObject
                | Ty::Object(_)
                | Ty::ModuleNamespace(_)
                | Ty::Array(_)
                | Ty::Tuple(_)
                | Ty::TypeReference(_)
        ),
        TypeofWitness::Function => matches!(ty, Ty::Function(_)),
    }
}

/// Return whether a constituent is currently known to be removed by a truthy check.
fn is_definitely_falsy(ty: Ty<'_>) -> bool {
    match ty {
        Ty::Undefined | Ty::Null => true,
        Ty::BooleanLiteral(boolean) => !boolean.value,
        _ => false,
    }
}

/// Return whether a symbol is written between the branch condition and reference location.
fn has_intervening_write(
    checker: &CheckerReturn<'_, '_>,
    node: NodeRef,
    symbol: SymbolRef,
    fact: BranchFact<'_>,
) -> bool {
    let query_span = checker.node_kind(node).span();
    checker
        .semantic(symbol.program_id)
        .symbol_references(symbol.symbol_id)
        .any(|reference| {
            if !reference.is_write() {
                return false;
            }
            let write_span = checker
                .nodes(symbol.program_id)
                .kind(reference.node_id())
                .span();
            write_span.start > fact.condition_span.end
                && write_span.start < query_span.start
                && fact.branch_span.contains_inclusive(write_span)
        })
}
