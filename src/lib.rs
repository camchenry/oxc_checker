use oxc_ast::{
    AstKind,
    ast::{
        ArrowFunctionExpression, BindingPattern, Expression, ForStatementLeft, FormalParameters,
        Function, FunctionBody, PropertyKey, ReturnStatement, TSSignature, TSTupleElement, TSType,
        TSTypeName, TSTypeQueryExprName, VariableDeclarator,
    },
};
use oxc_ast_visit::Visit;
use oxc_semantic::SymbolId;
use oxc_span::{GetSpan, Span};
use oxc_syntax::scope::ScopeFlags;
use std::collections::HashMap;

mod checker;
mod checker_impl;
mod evolving_arrays;
mod flow;
mod global_lib;
mod global_types;
pub mod program;
mod relations;
mod types;

use types::*;

#[derive(Debug, Clone, Copy)]
enum FunctionKind<'a> {
    Function(&'a Function<'a>),
    ArrowFunction(&'a ArrowFunctionExpression<'a>),
}

impl<'a> FunctionKind<'a> {
    fn returns_promise(self) -> bool {
        match self {
            FunctionKind::Function(function) => function.r#async && !function.generator,
            FunctionKind::ArrowFunction(function) => function.r#async,
        }
    }
}

struct ReturnExpressionVisitor<'a> {
    expressions: Vec<&'a Expression<'a>>,
}

impl<'a> ReturnExpressionVisitor<'a> {
    /// Collect return expressions from this function body, ignoring nested functions.
    fn expressions_in_body(body: &'a FunctionBody<'a>) -> Vec<&'a Expression<'a>> {
        let mut visitor = Self {
            expressions: Vec::new(),
        };
        visitor.visit_function_body(body);
        visitor.expressions
    }
}

impl<'a> Visit<'a> for ReturnExpressionVisitor<'a> {
    fn visit_return_statement(&mut self, statement: &ReturnStatement<'a>) {
        if let Some(argument) = statement.argument.as_ref() {
            self.expressions.push(self.alloc(argument));
        }
    }

    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(&mut self, _function: &ArrowFunctionExpression<'a>) {}
}

fn infer_type_parameter_from_types<'a>(
    parameter_type: &Ty<'a>,
    argument_type: &Ty<'a>,
    type_parameters: &[&'a str],
    substitutions: &mut HashMap<&'a str, Ty<'a>>,
) {
    match (parameter_type, argument_type) {
        (Ty::Union(parameter_union), _) => {
            infer_type_parameter_from_union(
                parameter_union.types.iter().copied(),
                argument_type,
                type_parameters,
                substitutions,
            );
        }
        (Ty::TypeReference(reference), _)
            if reference.type_arguments.is_empty() && type_parameters.contains(&reference.name) =>
        {
            match substitutions.get(reference.name) {
                Some(existing) if existing != argument_type => {
                    substitutions.insert(reference.name, Ty::any());
                }
                Some(_) => {}
                None => {
                    substitutions.insert(reference.name, *argument_type);
                }
            }
        }
        (Ty::TypeReference(parameter_reference), Ty::TypeReference(argument_reference))
            if parameter_reference.name == argument_reference.name =>
        {
            for (parameter_type, argument_type) in parameter_reference
                .type_arguments
                .iter()
                .zip(argument_reference.type_arguments.iter())
            {
                infer_type_parameter_from_types(
                    parameter_type,
                    argument_type,
                    type_parameters,
                    substitutions,
                );
            }
        }
        (Ty::Object(parameter_object), Ty::Object(argument_object)) => {
            for parameter_property in &parameter_object.properties {
                if let Some(argument_property) =
                    argument_object.properties.iter().find(|argument_property| {
                        argument_property.name == parameter_property.name
                            && argument_property.computed == parameter_property.computed
                    })
                {
                    infer_type_parameter_from_types(
                        &parameter_property.ty,
                        &argument_property.ty,
                        type_parameters,
                        substitutions,
                    );
                }
            }
        }
        (Ty::Function(parameter_function), Ty::Function(argument_function)) => {
            for (parameter, argument) in parameter_function
                .parameters
                .iter()
                .zip(argument_function.parameters.iter())
            {
                infer_type_parameter_from_types(
                    &parameter.ty,
                    &argument.ty,
                    type_parameters,
                    substitutions,
                );
            }
            infer_type_parameter_from_types(
                &parameter_function.return_type,
                &argument_function.return_type,
                type_parameters,
                substitutions,
            );
        }
        _ => {}
    }
}

fn infer_type_parameter_from_union<'a>(
    parameter_types: impl IntoIterator<Item = Ty<'a>>,
    argument_type: &Ty<'a>,
    type_parameters: &[&'a str],
    substitutions: &mut HashMap<&'a str, Ty<'a>>,
) {
    let parameter_types = parameter_types
        .into_iter()
        .filter(|ty| !matches!(ty, Ty::Null | Ty::Undefined | Ty::Never))
        .collect::<Vec<_>>();

    let candidates = match argument_type {
        Ty::Function(_) => parameter_types
            .iter()
            .copied()
            .filter(|ty| matches!(ty, Ty::Function(_)))
            .collect::<Vec<_>>(),
        Ty::TypeReference(argument_reference) => parameter_types
            .iter()
            .copied()
            .filter(|ty| {
                matches!(ty, Ty::TypeReference(parameter_reference) if parameter_reference.name == argument_reference.name)
            })
            .collect::<Vec<_>>(),
        _ => Vec::new(),
    };

    let candidates = if candidates.is_empty() {
        parameter_types
            .iter()
            .copied()
            .filter(|ty| {
                matches!(ty, Ty::TypeReference(reference) if reference.type_arguments.is_empty() && type_parameters.contains(&reference.name))
            })
            .collect::<Vec<_>>()
    } else {
        candidates
    };

    let candidates = if candidates.is_empty() {
        parameter_types
    } else {
        candidates
    };

    for candidate in candidates {
        infer_type_parameter_from_types(&candidate, argument_type, type_parameters, substitutions);
    }
}

fn property_key_name_str<'a>(key: &PropertyKey<'a>) -> Option<&'a str> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.name.as_str()),
        PropertyKey::Identifier(identifier) => Some(identifier.name.as_str()),
        PropertyKey::NumericLiteral(literal) => literal.raw.as_ref().map(|raw| raw.as_str()),
        PropertyKey::StringLiteral(literal) => Some(literal.value.as_str()),
        _ => None,
    }
}

fn index_type_to_property_name<'a>(arena: CheckerArena<'a>, ty: Ty<'a>) -> Option<&'a str> {
    match ty {
        Ty::StringLiteral(literal) => Some(literal.value),
        Ty::NumberLiteral(literal) => Some(literal.value),
        Ty::BooleanLiteral(value) => Some(if value { "true" } else { "false" }),
        Ty::TemplateLiteral(template) if template.expressions.is_empty() => {
            Some(template.quasis[0].value)
        }
        Ty::TypeReference(reference) if reference.type_arguments.is_empty() => Some(reference.name),
        Ty::String => Some(arena.str("string")),
        Ty::Number => Some(arena.str("number")),
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

fn ts_type_contains_infer(ty: &TSType<'_>) -> bool {
    match ty {
        TSType::TSInferType(_) => true,
        TSType::TSArrayType(array) => ts_type_contains_infer(&array.element_type),
        TSType::TSTupleType(tuple) => tuple.element_types.iter().any(|element| match element {
            TSTupleElement::TSRestType(rest) => ts_type_contains_infer(&rest.type_annotation),
            TSTupleElement::TSOptionalType(optional) => {
                ts_type_contains_infer(&optional.type_annotation)
            }
            _ => element.as_ts_type().is_some_and(ts_type_contains_infer),
        }),
        TSType::TSUnionType(union) => union.types.iter().any(|ty| ts_type_contains_infer(ty)),
        TSType::TSIntersectionType(intersection) => intersection
            .types
            .iter()
            .any(|ty| ts_type_contains_infer(ty)),
        TSType::TSParenthesizedType(parenthesized) => {
            ts_type_contains_infer(&parenthesized.type_annotation)
        }
        TSType::TSTypeOperatorType(operator) => ts_type_contains_infer(&operator.type_annotation),
        TSType::TSIndexedAccessType(indexed_access) => {
            ts_type_contains_infer(&indexed_access.object_type)
                || ts_type_contains_infer(&indexed_access.index_type)
        }
        TSType::TSConditionalType(conditional) => {
            ts_type_contains_infer(&conditional.check_type)
                || ts_type_contains_infer(&conditional.extends_type)
                || ts_type_contains_infer(&conditional.true_type)
                || ts_type_contains_infer(&conditional.false_type)
        }
        TSType::TSTypeReference(reference) => {
            reference
                .type_arguments
                .as_ref()
                .is_some_and(|type_arguments| {
                    type_arguments
                        .params
                        .iter()
                        .any(|ty| ts_type_contains_infer(ty))
                })
        }
        TSType::TSFunctionType(function) => {
            formal_parameters_contain_infer(function.params.as_ref())
                || ts_type_contains_infer(&function.return_type.type_annotation)
        }
        TSType::TSTypeLiteral(type_literal) => {
            type_literal.members.iter().any(ts_signature_contains_infer)
        }
        TSType::TSMappedType(mapped) => {
            ts_type_contains_infer(&mapped.constraint)
                || mapped
                    .name_type
                    .as_ref()
                    .is_some_and(|ty| ts_type_contains_infer(ty))
                || mapped
                    .type_annotation
                    .as_ref()
                    .is_some_and(|ty| ts_type_contains_infer(ty))
        }
        TSType::TSTypePredicate(predicate) => predicate
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation)),
        _ => false,
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

fn ts_signature_contains_infer(signature: &TSSignature<'_>) -> bool {
    match signature {
        TSSignature::TSPropertySignature(property) => property
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation)),
        TSSignature::TSMethodSignature(method) => {
            formal_parameters_contain_infer(method.params.as_ref())
                || method
                    .return_type
                    .as_deref()
                    .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
        }
        TSSignature::TSCallSignatureDeclaration(signature) => {
            formal_parameters_contain_infer(signature.params.as_ref())
                || signature
                    .return_type
                    .as_deref()
                    .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
        }
        TSSignature::TSConstructSignatureDeclaration(signature) => {
            formal_parameters_contain_infer(signature.params.as_ref())
                || signature
                    .return_type
                    .as_deref()
                    .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
        }
        _ => false,
    }
}

fn formal_parameters_contain_infer(parameters: &FormalParameters<'_>) -> bool {
    parameters.items.iter().any(|parameter| {
        parameter
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
    }) || parameters.rest.as_ref().is_some_and(|parameter| {
        parameter
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
    })
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClassMemberResolution {
    program_id: program::ProgramId,
    class_name: String,
    property_name: String,
    is_static: bool,
}

fn is_number_index_type(ty: Ty<'_>) -> bool {
    matches!(ty, Ty::Number | Ty::NumberLiteral(_))
}

fn is_promise_like_type_reference(name: &str) -> bool {
    matches!(name, "Promise" | "PromiseLike")
}

fn is_iterable_type_reference(name: &str) -> bool {
    matches!(
        name,
        "AsyncIterable"
            | "AsyncIterableIterator"
            | "AsyncIterator"
            | "AsyncIteratorObject"
            | "Iterable"
            | "IterableIterator"
            | "Iterator"
            | "IteratorObject"
            | "ArrayIterator"
            | "MapIterator"
            | "SetIterator"
    )
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

fn tuple_element_type(element: TupleElement<'_>) -> Ty<'_> {
    match element {
        TupleElement::Regular(ty) | TupleElement::Rest(ty) | TupleElement::Optional(ty) => ty,
    }
}

fn tuple_element_type_at_index<'a>(object_type: &Ty<'a>, index: usize) -> Option<Ty<'a>> {
    let Ty::Tuple(tuple) = object_type else {
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
                    return Some(ty.array_element_type().unwrap_or(*ty));
                }
            }
        }
    }

    Some(Ty::undefined())
}

fn index_signature_key_types<'a>(constraint: Ty<'a>) -> Option<Vec<Ty<'a>>> {
    match constraint {
        Ty::String => Some(vec![Ty::string()]),
        Ty::Number => Some(vec![Ty::number()]),
        Ty::Symbol => Some(vec![Ty::symbol()]),
        Ty::Union(union) => {
            let mut key_types = Vec::new();
            for ty in &union.types {
                let keys = index_signature_key_types(*ty)?;
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
pub mod benchmark_support {
    use crate::checker::{Checker, CheckerBuilder, NodeRef};

    use super::{AstKind, program};
    use oxc_semantic::NodeId;

    pub struct CheckPlan {
        program_id: program::ProgramId,
        queries: Vec<CheckQuery>,
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
mod test {
    use super::*;
    use crate::checker::{Checker, CheckerBuilder, NodeRef, SymbolRef};
    use crate::checker_impl::UNDEFINED_IDENT;
    use crate::program::ProgramHost;
    use oxc_allocator::Allocator;
    use oxc_str::Ident;
    use std::{
        collections::HashMap,
        path::{Path, PathBuf},
    };

    struct TestProgramHost {
        cwd: PathBuf,
        files: HashMap<PathBuf, String>,
    }

    impl TestProgramHost {
        fn new(cwd: impl Into<PathBuf>) -> Self {
            Self {
                cwd: cwd.into(),
                files: HashMap::new(),
            }
        }

        fn add_file(mut self, path: impl AsRef<Path>, source_text: &str) -> Self {
            let path = self.canonicalize_path(path.as_ref());
            self.files.insert(path, source_text.to_string());
            self
        }
    }

    impl program::ProgramHost for TestProgramHost {
        fn read_source(&self, path: &Path) -> program::ProgramStoreResult<String> {
            self.files
                .get(&self.canonicalize_path(path))
                .cloned()
                .ok_or_else(|| program::ProgramStoreError::ReadSource {
                    path: path.to_path_buf(),
                    message: "file not found".to_string(),
                })
        }

        fn canonicalize_path(&self, path: &Path) -> PathBuf {
            if path.is_absolute() {
                path.to_path_buf()
            } else {
                self.cwd.join(path)
            }
        }

        fn resolve_module(
            &self,
            _containing_file: &Path,
            specifier: &str,
        ) -> program::HostModuleResolution {
            program::HostModuleResolution::Missing(specifier.to_string())
        }
    }

    struct ParseAndCheck<'a> {
        store: program::ProgramStore<'a>,
        program_id: program::ProgramId,
    }

    fn parse_and_check_source<'a>(
        allocator: &'a Allocator,
        source_text: &str,
    ) -> ParseAndCheck<'a> {
        let host = TestProgramHost::new("/project").add_file("/project/main.ts", source_text);
        let store = program::ProgramStoreBuilder::new(allocator, host)
            .add_root_file("/project/main.ts")
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/main.ts")).unwrap();
        assert_eq!(
            store
                .entry(program_id)
                .unwrap()
                .semantic()
                .nodes()
                .program()
                .source_text,
            source_text
        );

        ParseAndCheck { store, program_id }
    }

    fn get_global_symbol_type<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let scoping = ret
            .store
            .entry(ret.program_id)
            .unwrap()
            .semantic()
            .scoping();
        let symbol_id = scoping.get_root_binding(Ident::from(name)).unwrap();
        checker.get_type_of_symbol(SymbolRef::new(ret.program_id, symbol_id))
    }

    fn get_type_alias_type<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let alias = semantic
            .nodes()
            .iter()
            .find_map(|node| match node.kind() {
                AstKind::TSTypeAliasDeclaration(alias) if alias.id.name == Ident::from(name) => {
                    Some(alias)
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("expected type alias `{name}`"));
        checker.get_type_of_type_alias_declaration(ret.program_id, alias)
    }

    fn get_symbol_type_in_function<'a>(
        ret: &ParseAndCheck<'a>,
        func_name: &str,
        param_name: &str,
    ) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let scoping = semantic.scoping();
        let func = scoping
            .scope_descendants_from_root()
            .find(|scope_id| {
                if let AstKind::Function(func) =
                    semantic.nodes().kind(scoping.get_node_id(*scope_id))
                {
                    func.name() == Some(Ident::from(func_name))
                } else {
                    false
                }
            })
            .unwrap();
        let symbol_id = scoping.get_binding(func, Ident::from(param_name)).unwrap();
        checker.get_type_of_symbol(SymbolRef::new(ret.program_id, symbol_id))
    }

    fn get_first_symbol_type<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let scoping = semantic.scoping();
        let symbol_id = scoping
            .scope_descendants_from_root()
            .find_map(|scope_id| scoping.get_binding(scope_id, Ident::from(name)))
            .unwrap();
        checker.get_type_of_symbol(SymbolRef::new(ret.program_id, symbol_id))
    }

    fn get_global_type<'a>(
        ret: &ParseAndCheck<'a>,
        program_id: program::ProgramId,
        name: &str,
    ) -> Ty<'a> {
        let checker = CheckerBuilder::new().build(&ret.store);
        checker.get_global_type(program_id, name)
    }

    fn get_object_property_types<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Vec<Ty<'a>> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::ObjectProperty(property)
                    if property_key_name_str(&property.key) == Some(name) =>
                {
                    Some(checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)))
                }
                _ => None,
            })
            .collect()
    }

    fn get_ts_method_signature_types(ret: &ParseAndCheck<'_>, name: &str) -> Vec<String> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::TSMethodSignature(method)
                    if property_key_name_str(&method.key) == Some(name) =>
                {
                    Some(
                        checker
                            .get_type_at_location(NodeRef::new(ret.program_id, node_id))
                            .to_type_string(),
                    )
                }
                _ => None,
            })
            .collect()
    }

    fn get_ts_property_signature_types(ret: &ParseAndCheck<'_>, name: &str) -> Vec<String> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::TSPropertySignature(property)
                    if property_key_name_str(&property.key) == Some(name) =>
                {
                    Some(
                        checker
                            .get_type_at_location(NodeRef::new(ret.program_id, node_id))
                            .to_type_string(),
                    )
                }
                _ => None,
            })
            .collect()
    }

    fn get_identifier_reference_types<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Vec<Ty<'a>> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::IdentifierReference(identifier)
                    if identifier.name == Ident::from(name) =>
                {
                    Some(checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)))
                }
                _ => None,
            })
            .collect()
    }

    fn get_static_member_expression_types<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Vec<Ty<'a>> {
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| match node.kind() {
                AstKind::StaticMemberExpression(member)
                    if member.property.name == Ident::from(name) =>
                {
                    Some(checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)))
                }
                _ => None,
            })
            .collect()
    }

    fn arena<'a>(ret: &ParseAndCheck<'a>) -> CheckerArena<'a> {
        CheckerArena::new(ret.store.allocator())
    }

    #[test]
    fn semantic_cfg_is_built_for_programs() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "if (value) { value; }");

        assert!(
            ret.store
                .entry(ret.program_id)
                .unwrap()
                .semantic()
                .cfg()
                .is_some()
        );
    }

    #[test]
    fn default_lib_provides_global_type_symbols() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const x = 1;");
        let checker = CheckerBuilder::new().build(&ret.store);

        for (name, constructor_type) in [
            ("Array", "ArrayConstructor"),
            ("Promise", "PromiseConstructor"),
            ("Map", "MapConstructor"),
            ("Set", "SetConstructor"),
            ("Symbol", "SymbolConstructor"),
            ("Object", "ObjectConstructor"),
        ] {
            assert!(
                checker
                    .get_type_symbol_for_name(ret.program_id, name)
                    .is_some(),
                "expected default lib to provide global type `{name}`"
            );
            let value_symbol = checker
                .get_value_symbol_for_name(ret.program_id, name)
                .unwrap_or_else(|| panic!("expected default lib to provide global value `{name}`"));
            assert_eq!(
                checker.get_type_of_symbol(value_symbol).to_type_string(),
                constructor_type
            );
        }
    }

    #[test]
    fn without_default_lib_has_no_global_type_symbols() {
        let allocator = Allocator::default();
        let host = TestProgramHost::new("/project").add_file("/project/main.ts", "const x = 1;");
        let store = program::ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/main.ts")
            .without_default_lib()
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/main.ts")).unwrap();
        let checker = CheckerBuilder::new().build(&store);

        assert_eq!(store.entries().len(), 1);
        assert!(
            checker
                .get_type_symbol_for_name(program_id, "Array")
                .is_none()
        );
        assert!(
            checker
                .get_value_symbol_for_name(program_id, "Array")
                .is_none()
        );
    }

    #[test]
    fn global_symbol_table_resolves_other_root_script_declarations() {
        let allocator = Allocator::default();
        let host = TestProgramHost::new("/project")
            .add_file("/project/main.ts", "const value = shared;")
            .add_file(
                "/project/globals.ts",
                "interface Shared { count: number } declare const shared: Shared;",
            );
        let store = program::ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/main.ts")
            .add_root_file("/project/globals.ts")
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/main.ts")).unwrap();
        let checker = CheckerBuilder::new().build(&store);
        let scoping = store.entry(program_id).unwrap().semantic().scoping();
        let value_symbol_id = scoping.get_root_binding(Ident::from("value")).unwrap();

        assert!(
            checker
                .get_type_symbol_for_name(program_id, "Shared")
                .is_some()
        );
        assert_eq!(
            checker
                .get_type_of_symbol(SymbolRef::new(program_id, value_symbol_id))
                .to_type_string(),
            "Shared"
        );
    }

    #[test]
    fn local_value_symbols_shadow_default_lib_globals() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const Array = 1;
        const value = Array;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "value"),
            Ty::number_literal(arena, "1")
        );
    }

    #[test]
    fn local_undefined_binding_wins_before_global_undefined_fallback() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const undefined = 1;
        const value = undefined;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "value"),
            Ty::number_literal(arena, "1")
        );
        assert_eq!(
            get_identifier_reference_types(&ret, "undefined"),
            vec![Ty::number_literal(arena, "1")]
        );
    }

    #[test]
    fn parameter_named_undefined_shadows_global_undefined() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        function shadow(undefined: number) {
            const inside = undefined;
        }
        const outside = undefined;
        ",
        );

        assert_eq!(get_first_symbol_type(&ret, "inside"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "outside"), Ty::undefined());
        assert_eq!(
            get_identifier_reference_types(&ret, "undefined"),
            vec![Ty::number(), Ty::undefined()]
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "shadow", "undefined"),
            Ty::number()
        );
    }

    #[test]
    fn value_position_global_identifiers_resolve_to_constructor_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const arrayCtor = Array;
        const promiseCtor = Promise;
        const mapCtor = Map;
        const setCtor = Set;
        const symbolCtor = Symbol;
        const objectCtor = Object;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "arrayCtor"),
            Ty::type_reference(arena, "ArrayConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "promiseCtor"),
            Ty::type_reference(arena, "PromiseConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "mapCtor"),
            Ty::type_reference(arena, "MapConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "setCtor"),
            Ty::type_reference(arena, "SetConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "symbolCtor"),
            Ty::type_reference(arena, "SymbolConstructor", [])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "objectCtor"),
            Ty::type_reference(arena, "ObjectConstructor", [])
        );
    }

    #[test]
    fn value_position_global_constructors_expose_members_and_construct_signatures() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const keys = Object.keys({ a: 1 });
        const values = new Array<number>(1);
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "keys"),
            Ty::array(arena, Ty::string())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "values"),
            Ty::array(arena, Ty::number())
        );
    }

    #[test]
    fn global_type_reference_locations_resolve_symbols() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type Values = Array<number>;
        type Later = Promise<string>;
        ",
        );
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();

        let type_reference_type = |name: &str| {
            let (node_id, _) = semantic
                .nodes()
                .iter_enumerated()
                .find_map(|(node_id, node)| match node.kind() {
                    AstKind::TSTypeReference(reference)
                        if matches!(
                            &reference.type_name,
                            TSTypeName::IdentifierReference(identifier)
                                if identifier.name == Ident::from(name)
                        ) =>
                    {
                        Some((node_id, reference))
                    }
                    _ => None,
                })
                .unwrap_or_else(|| panic!("expected type reference `{name}`"));
            let symbol = checker
                .get_symbol_at_location(NodeRef::new(ret.program_id, node_id))
                .unwrap_or_else(|| panic!("expected symbol for type reference `{name}`"));
            checker.get_type_of_symbol(symbol).to_type_string()
        };

        assert_eq!(type_reference_type("Array"), "ArrayConstructor");
        assert_eq!(type_reference_type("Promise"), "PromiseConstructor");
    }

    #[test]
    fn default_lib_entries_are_marked_as_lib() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const x = 1;");

        let lib_count = ret
            .store
            .entries()
            .iter()
            .filter(|entry| entry.is_lib())
            .count();
        assert_eq!(lib_count, crate::global_lib::DEFAULT_LIB_FILES.len());

        let user_entry = ret.store.entry(ret.program_id).unwrap();
        assert!(!user_entry.is_lib());
    }

    #[test]
    fn flow_narrows_truthy_if_branch() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const x: string | undefined;
        if (x) {
            x;
        } else {
            x;
        }
        ",
        );

        let reference_types = get_identifier_reference_types(&ret, "x");
        assert_eq!(reference_types.len(), 3);
        assert_eq!(
            reference_types[0],
            Ty::union(arena(&ret), [Ty::string(), Ty::undefined()])
        );
        assert_eq!(reference_types[1], Ty::string());
        assert_eq!(
            reference_types[2],
            Ty::union(arena(&ret), [Ty::string(), Ty::undefined()])
        );
    }

    #[test]
    fn flow_narrows_typeof_if_branches() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const y: string | number | boolean;
        if (typeof y === 'string') {
            y;
        } else {
            y;
        }
        ",
        );

        let reference_types = get_identifier_reference_types(&ret, "y");
        assert_eq!(reference_types.len(), 3);
        assert_eq!(
            reference_types[0],
            Ty::union(arena(&ret), [Ty::string(), Ty::number(), Ty::boolean()])
        );
        assert_eq!(reference_types[1], Ty::string());
        assert_eq!(
            reference_types[2],
            Ty::union(arena(&ret), [Ty::number(), Ty::boolean()])
        );
    }

    #[test]
    fn flow_narrows_typeof_conditional_expression_arms() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const y: string | number | boolean;
        const z = typeof y === 'string' ? y : undefined;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "z"),
            Ty::union(arena, [Ty::string(), Ty::undefined()])
        );
        assert_eq!(
            get_identifier_reference_types(&ret, "y"),
            vec![
                Ty::union(arena, [Ty::string(), Ty::number(), Ty::boolean()]),
                Ty::string(),
            ]
        );
    }

    #[test]
    fn flow_narrows_undefined_equality_conditional_expression_arms() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        function usePrevious<TData>(previous: TData | undefined, initialValue: TData) {
            const value = previous === undefined ? initialValue : previous;
        }
        ",
        );

        assert_eq!(
            get_first_symbol_type(&ret, "value").to_type_string(),
            "TData | (TData & ({} | null))"
        );
        assert_eq!(
            get_identifier_reference_types(&ret, "previous")
                .into_iter()
                .map(Ty::to_type_string)
                .collect::<Vec<_>>(),
            vec![
                "TData | undefined".to_string(),
                "TData & ({} | null)".to_string(),
            ]
        );
    }

    #[test]
    fn flow_write_invalidates_previous_narrowing() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        let y: string | number;
        if (typeof y === 'string') {
            y = 1;
            y;
        }
        ",
        );

        let reference_types = get_identifier_reference_types(&ret, "y");
        assert_eq!(reference_types.len(), 3);
        assert_eq!(
            reference_types[0],
            Ty::union(arena(&ret), [Ty::string(), Ty::number()])
        );
        assert_eq!(reference_types[1], Ty::string());
        assert_eq!(
            reference_types[2],
            Ty::union(arena(&ret), [Ty::string(), Ty::number()])
        );
    }

    #[test]
    fn flow_evolves_empty_array_locals_from_mutations() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        let values = [];
        const before = values;
        values.push(1);
        const afterPush = values;
        values[1] = 'ready';
        const afterWrite = values;
        values = [false];
        const afterReset = values;
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "before"),
            Ty::array(arena, Ty::any())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "afterPush"),
            Ty::array(arena, Ty::number())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "afterWrite"),
            Ty::array(arena, Ty::union(arena, [Ty::number(), Ty::string()]))
        );
        assert_eq!(
            get_global_symbol_type(&ret, "afterReset"),
            Ty::array(arena, Ty::boolean())
        );
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn type_enum_is_pointer_sized_payload_plus_discriminant() {
        assert_eq!(std::mem::size_of::<Ty>(), 16);
    }

    #[cfg(target_pointer_width = "32")]
    #[test]
    fn type_enum_is_pointer_sized_payload_plus_discriminant() {
        assert_eq!(std::mem::size_of::<Ty>(), 8);
    }

    #[test]
    fn assignability_handles_basic_and_structural_types() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);

        assert!(relations::is_assignable_to(Ty::number(), Ty::number()));
        assert!(relations::is_assignable_to(Ty::number(), Ty::any()));
        assert!(relations::is_assignable_to(Ty::string(), Ty::unknown()));
        assert!(!relations::is_assignable_to(Ty::number(), Ty::string()));
        assert!(relations::is_assignable_to(
            Ty::number_literal(arena, "1"),
            Ty::number()
        ));
        assert!(relations::is_assignable_to(
            Ty::array(arena, Ty::number()),
            Ty::array(arena, Ty::number())
        ));

        let source = Ty::object(
            arena,
            [
                Ty::property("x", Ty::number()),
                Ty::property("y", Ty::string()),
            ],
        );
        let target = Ty::object(arena, [Ty::property("x", Ty::number())]);

        assert!(relations::is_assignable_to(source, target));
        assert!(!relations::is_assignable_to(target, source));
    }

    #[test]
    fn simple_declared_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const a: number = 1;
        const b: string = 'hello';
        const c: boolean = true;
        const d: bigint = 1n;
        const e: undefined = undefined;
        const f: null = null;
        const g: any = 1;
        const h: unknown = 1;
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "a"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "b"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "c"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "d"), Ty::bigint());
        assert_eq!(get_global_symbol_type(&ret, "e"), Ty::undefined());
        assert_eq!(get_global_symbol_type(&ret, "f"), Ty::null());
        assert_eq!(get_global_symbol_type(&ret, "g"), Ty::any());
        assert_eq!(get_global_symbol_type(&ret, "h"), Ty::unknown());
    }

    #[test]
    fn destructured_parameters_preserve_pattern_and_property_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                type BaseStreamedQueryParams<TQueryFnData> = {
                    streamFn: (context: TQueryFnData) => TQueryFnData;
                    refetchMode?: 'append' | 'reset' | 'replace';
                };
                type SimpleStreamedQueryParams<TQueryFnData> =
                    BaseStreamedQueryParams<TQueryFnData> & {
                        reducer?: never;
                        initialValue?: never;
                    };
                type ReducibleStreamedQueryParams<TQueryFnData, TData> =
                    BaseStreamedQueryParams<TQueryFnData> & {
                        reducer: (acc: TData, chunk: TQueryFnData) => TData;
                        initialValue: TData;
                    };
                type StreamedQueryParams<TQueryFnData, TData> =
                    | SimpleStreamedQueryParams<TQueryFnData>
                    | ReducibleStreamedQueryParams<TQueryFnData, TData>;

                function streamedQuery<TQueryFnData, TData>({
                    streamFn,
                    refetchMode = 'reset',
                    reducer = (items, chunk) => items,
                    initialValue = {} as TData,
                }: StreamedQueryParams<TQueryFnData, TData>): TData {
                    return initialValue;
                }
                ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "streamedQuery").to_type_string(),
            "<TQueryFnData, TData>({ streamFn, refetchMode, reducer, initialValue, }: StreamedQueryParams<TQueryFnData, TData>) => TData"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "streamFn").to_type_string(),
            "(context: TQueryFnData) => TQueryFnData"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "refetchMode").to_type_string(),
            "\"append\" | \"reset\" | \"replace\""
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "reducer").to_type_string(),
            "(acc: TData, chunk: TQueryFnData) => TData"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "initialValue").to_type_string(),
            "TData"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "items"),
            Ty::type_reference(arena(&ret), "TData", std::iter::empty())
        );
        assert_eq!(
            get_first_symbol_type(&ret, "chunk"),
            Ty::type_reference(arena(&ret), "TQueryFnData", std::iter::empty())
        );
    }

    #[test]
    fn object_literal_call_argument_contextually_types_callback_property_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                type QueryKey = readonly unknown[];

                type BaseStreamedQueryParams<TQueryFnData, TQueryKey extends QueryKey> = {
                    streamFn: () => AsyncIterable<TQueryFnData>;
                };
                type SimpleStreamedQueryParams<TQueryFnData, TQueryKey extends QueryKey> =
                    BaseStreamedQueryParams<TQueryFnData, TQueryKey> & {
                        reducer?: never;
                        initialValue?: never;
                    };
                type ReducibleStreamedQueryParams<TQueryFnData, TData, TQueryKey extends QueryKey> =
                    BaseStreamedQueryParams<TQueryFnData, TQueryKey> & {
                        reducer: (acc: TData, chunk: TQueryFnData) => TData;
                        initialValue: TData;
                    };
                type StreamedQueryParams<TQueryFnData, TData, TQueryKey extends QueryKey> =
                    | SimpleStreamedQueryParams<TQueryFnData, TQueryKey>
                    | ReducibleStreamedQueryParams<TQueryFnData, TData, TQueryKey>;

                function streamedQuery<TQueryFnData, TData, TQueryKey extends QueryKey>(
                    params: StreamedQueryParams<TQueryFnData, TData, TQueryKey>
                ): TData {
                    return params.initialValue as TData;
                }

                interface InfiniteData<TData, TPageParam = unknown> {
                    pages: Array<TData>;
                    pageParams: Array<TPageParam>;
                }

                type Todo = { id: number; title: string };
                declare const todoStream: AsyncIterable<Todo>;
                const pageParam: number = 1;

                const queryFn = streamedQuery<Todo, InfiniteData<Todo, number>, readonly ['todos']>({
                    streamFn: () => todoStream,
                    reducer: (data, todo) => ({
                        pages: [...data.pages, todo],
                        pageParams: [...data.pageParams, pageParam],
                    }),
                    initialValue: { pages: [], pageParams: [] },
                });
                ",
        );
        let arena = arena(&ret);
        let todo_type = Ty::type_reference(arena, "Todo", std::iter::empty());
        let infinite_data_type =
            Ty::type_reference(arena, "InfiniteData", [todo_type, Ty::number()]);

        assert_eq!(get_first_symbol_type(&ret, "data"), infinite_data_type);
        assert_eq!(get_first_symbol_type(&ret, "todo"), todo_type);
        assert_eq!(
            get_object_property_types(&ret, "reducer")[0].to_type_string(),
            "(data: InfiniteData<Todo, number>, todo: Todo) => { pages: Todo[]; pageParams: number[]; }"
        );
        assert!(get_object_property_types(&ret, "pages").contains(&Ty::array(arena, todo_type)));
        assert!(get_object_property_types(&ret, "pages").contains(&Ty::array(arena, Ty::never())));
        assert!(
            get_object_property_types(&ret, "pageParams").contains(&Ty::array(arena, Ty::never()))
        );
    }

    #[test]
    fn returned_function_expression_uses_annotated_return_context_for_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                type QueryFunctionContext<TQueryKey, TPageParam = never> =
                    [TPageParam] extends [never]
                        ? { queryKey: TQueryKey; pageParam?: unknown }
                        : { queryKey: TQueryKey; pageParam: TPageParam };
                type QueryFunction<T, TQueryKey, TPageParam = never> =
                    (queryContext: QueryFunctionContext<TQueryKey, TPageParam>) => T | Promise<T>;

                function makeQuery<TData, TQueryKey>(): QueryFunction<TData, TQueryKey> {
                    return async (context) => undefined as TData;
                }
                ",
        );

        assert_eq!(
            get_first_symbol_type(&ret, "context").to_type_string(),
            "{ queryKey: TQueryKey; pageParam?: unknown; }"
        );
    }

    #[test]
    fn declared_function_type_parameters_expand_conditional_alias_annotations() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                type QueryFunctionContext<TQueryKey, TPageParam = never> =
                    [TPageParam] extends [never]
                        ? { queryKey: TQueryKey; pageParam?: unknown }
                        : { queryKey: TQueryKey; pageParam: TPageParam };

                type BaseStreamedQueryParams<TQueryKey> = {
                    streamFn: (context: QueryFunctionContext<TQueryKey>) => void;
                };

                function useParams<TQueryKey>({ streamFn }: BaseStreamedQueryParams<TQueryKey>) {
                    return streamFn;
                }
                ",
        );

        assert_eq!(
            get_first_symbol_type(&ret, "context").to_type_string(),
            "{ queryKey: TQueryKey; pageParam?: unknown; }"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "useParams", "streamFn").to_type_string(),
            "(context: { queryKey: TQueryKey; pageParam?: unknown; }) => void"
        );
    }

    #[test]
    fn streamed_query_style_aliases_render_at_use_sites() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
                interface Register {}
                interface QueryClient {}
                interface AbortSignal {}
                interface Error {}
                type Todo = { id: number; title: string };
                declare const dataTagSymbol: unique symbol;
                declare const dataTagErrorSymbol: unique symbol;
                type AnyDataTag = { [dataTagSymbol]: any; [dataTagErrorSymbol]: any };
                type DataTag<TType, TValue, TError> = TType extends AnyDataTag
                    ? TType
                    : TType & { [dataTagSymbol]: TValue; [dataTagErrorSymbol]: TError };
                type InferDataFromTag<TQueryFnData, TTaggedQueryKey> =
                    TTaggedQueryKey extends DataTag<unknown, infer TaggedValue, unknown>
                        ? TaggedValue
                        : TQueryFnData;
                type TodoQueryKey = DataTag<readonly [\"todos\"], Todo[], Error>;
                type TaggedTodoData = InferDataFromTag<string, TodoQueryKey>;
                type QueryKey = Register extends { queryKey: infer TQueryKey }
                    ? TQueryKey extends readonly unknown[] ? TQueryKey : readonly unknown[]
                    : readonly unknown[];
                type QueryMeta = Register extends { queryMeta: infer TQueryMeta }
                    ? TQueryMeta extends Record<string, unknown> ? TQueryMeta : Record<string, unknown>
                    : Record<string, unknown>;
                type QueryFunctionContext<TQueryKey extends QueryKey = QueryKey, TPageParam = never> =
                    [TPageParam] extends [never]
                        ? { client: QueryClient; queryKey: TQueryKey; signal: AbortSignal; meta: QueryMeta | undefined; pageParam?: unknown; direction?: unknown }
                        : { client: QueryClient; queryKey: TQueryKey; signal: AbortSignal; pageParam: TPageParam; meta: QueryMeta | undefined };
                type QueryFunction<T = unknown, TQueryKey extends QueryKey = QueryKey, TPageParam = never> =
                    (context: QueryFunctionContext<TQueryKey, TPageParam>) => T;
                type OmitKeyof<TObject, TKey extends keyof TObject, TStrictly = 'strictly'> = Omit<TObject, TKey>;
                type StreamedQueryParams<TQueryFnData, TData, TQueryKey extends QueryKey> = {
                    streamFn: (context: QueryFunctionContext<TQueryKey>) => TQueryFnData;
                    initialValue: TData;
                };
                declare const numberedContext: QueryFunctionContext<readonly [\"todos\"], number>;
                const pageParam = numberedContext.pageParam;

                function streamedQuery<
                    TQueryFnData = unknown,
                    TData = Array<TQueryFnData>,
                    TQueryKey extends QueryKey = QueryKey,
                >({ streamFn, initialValue }: StreamedQueryParams<TQueryFnData, TData, TQueryKey>): QueryFunction<TData, TQueryKey> {
                    return (context) => {
                        const signalLessContext: OmitKeyof<typeof context, 'signal'> = {
                            client: context.client,
                            meta: context.meta,
                            queryKey: context.queryKey,
                        };
                        const meta = context.meta;
                        return initialValue;
                    };
                }
                ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "streamedQuery").to_type_string(),
            "<TQueryFnData = unknown, TData = TQueryFnData[], TQueryKey extends QueryKey = readonly unknown[]>({ streamFn, initialValue, }: StreamedQueryParams<TQueryFnData, TData, TQueryKey>) => QueryFunction<TData, TQueryKey>"
        );
        assert_eq!(
            get_type_alias_type(&ret, "QueryMeta").to_type_string(),
            "{ [x: string]: unknown; }"
        );
        assert_eq!(
            get_type_alias_type(&ret, "InferDataFromTag").to_type_string(),
            "TTaggedQueryKey extends { [dataTagSymbol]: infer TaggedValue; [dataTagErrorSymbol]: unknown; } ? TaggedValue : TQueryFnData"
        );
        assert_eq!(
            get_type_alias_type(&ret, "TaggedTodoData").to_type_string(),
            "Todo[]"
        );
        assert_eq!(
            get_ts_property_signature_types(&ret, "meta"),
            vec![
                "Record<string, unknown> | undefined",
                "Record<string, unknown> | undefined",
            ]
        );
        assert_eq!(get_global_symbol_type(&ret, "pageParam"), Ty::number());
        assert_eq!(
            get_first_symbol_type(&ret, "signalLessContext").to_type_string(),
            "OmitKeyof<{ client: QueryClient; queryKey: TQueryKey; signal: AbortSignal; meta: QueryMeta | undefined; pageParam?: unknown; direction?: unknown; }, \"signal\">"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "meta").to_type_string(),
            "Record<string, unknown> | undefined"
        );
    }

    #[test]
    fn unique_symbol_types_and_type_queries_render() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const dataTagSymbol: unique symbol;
        declare const aliasValue: typeof dataTagSymbol;
        declare const tagged: { [dataTagSymbol]: any };
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "dataTagSymbol").to_type_string(),
            "unique symbol"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "aliasValue").to_type_string(),
            "typeof dataTagSymbol"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "tagged").to_type_string(),
            "{ [dataTagSymbol]: any; }"
        );

        let ret = parse_and_check_source(
            &allocator,
            "
        declare const unsetMarker: unique symbol;
        type UnsetMarker = typeof unsetMarker;
        ",
        );

        assert_eq!(
            get_type_alias_type(&ret, "UnsetMarker").to_type_string(),
            "unique symbol"
        );
    }

    #[test]
    fn global_undefined_reference_has_type_at_location() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const value = [undefined];");
        let checker = CheckerBuilder::new().build(&ret.store);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let (node_id, _) = semantic
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| match node.kind() {
                AstKind::IdentifierReference(identifier) if identifier.name == UNDEFINED_IDENT => {
                    Some((node_id, identifier))
                }
                _ => None,
            })
            .unwrap();

        assert_eq!(
            checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)),
            Ty::undefined()
        );
    }

    #[test]
    fn declared_array_types_use_array_variant() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const values: number[] = [1, 2, 3];
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "values"),
            Ty::array(arena(&ret), Ty::number())
        );
    }

    #[test]
    fn global_array_type_references_use_array_variant() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const values: Array<number> = [1, 2, 3];
        const readonlyValues: ReadonlyArray<string> = ['a'];
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "values"),
            Ty::array(arena(&ret), Ty::number())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "readonlyValues"),
            Ty::readonly_array(arena(&ret), Ty::string())
        );
    }

    #[test]
    fn array_type_references_without_default_lib_stay_type_references() {
        let allocator = Allocator::default();
        let host = TestProgramHost::new("/project").add_file(
            "/project/main.ts",
            "const values: Array<number> = [1, 2, 3];",
        );
        let store = program::ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/main.ts")
            .without_default_lib()
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/main.ts")).unwrap();
        let expected_arena = CheckerArena::new(store.allocator());
        let checker = CheckerBuilder::new().build(&store);
        let symbol_id = store
            .entry(program_id)
            .unwrap()
            .semantic()
            .scoping()
            .get_root_binding(Ident::from("values"))
            .unwrap();

        assert_eq!(
            checker.get_type_of_symbol(SymbolRef::new(program_id, symbol_id)),
            Ty::type_reference(expected_arena, "Array", [Ty::number()])
        );
    }

    #[test]
    fn declared_tuple_types_preserve_rest_and_optional_element_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const variadic: [...string[], { huh: boolean }] = ['value', { huh: true }];
        const optional: [number?] = [];
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "variadic").to_type_string(),
            "[...string[], { huh: boolean; }]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "optional").to_type_string(),
            "[(number | undefined)?]"
        );
    }

    #[test]
    fn conditional_types_resolve_concrete_branches() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const yes: number extends number ? boolean : string = true;
        const no: number extends string ? boolean : string = 'no';
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "yes"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "no"), Ty::string());
    }

    #[test]
    fn conditional_types_preserve_unresolved_generic_checks() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const value: T extends string ? number : boolean;
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value").to_type_string(),
            "T extends string ? number : boolean"
        );
    }

    #[test]
    fn infer_types_resolve_when_concrete() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const value: string extends infer U ? U : never;
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value").to_type_string(),
            "string"
        );
    }

    #[test]
    fn type_alias_declarations_expand_top_level_alias_references() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type Pick<T, K extends keyof T> = { [P in K]: T[P] };
        type Exclude<T, U> = T extends U ? never : T;
        type Omit<T, K extends keyof any> = Pick<T, Exclude<keyof T, K>>;
        type OmitKeyof<TObject, TKey extends keyof TObject> = Omit<TObject, TKey>;
        ",
        );

        assert_eq!(
            get_type_alias_type(&ret, "OmitKeyof").to_type_string(),
            "{ [P in Exclude<keyof TObject, TKey>]: TObject[P]; }"
        );
    }

    #[test]
    fn type_literal_property_signatures_preserve_optional_modifier() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type Params = { refetchMode?: "append" | "reset" };
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Params").to_type_string(),
            "{ refetchMode?: \"append\" | \"reset\"; }"
        );
    }

    #[test]
    fn optional_mapped_type_aliases_include_undefined_and_drop_empty_intersection() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type OptionalFlat<O> = {
            [K in keyof O]?: O[K]
        } & {};
        type OptionalDeep<O> = {
            [K in keyof O]?: OptionalDeep<O[K]>
        };
        type OptionalPart<O> = {
            flat: OptionalFlat<O>
            deep: OptionalDeep<O>
        };
        ",
        );

        assert_eq!(
            get_type_alias_type(&ret, "OptionalFlat").to_type_string(),
            "{ [K in keyof O]?: O[K] | undefined; }"
        );
        assert_eq!(
            get_ts_property_signature_types(&ret, "flat"),
            vec!["{ [K in keyof O]?: O[K] | undefined; }"]
        );
        assert_eq!(
            get_ts_property_signature_types(&ret, "deep"),
            vec!["OptionalDeep<O>"]
        );
    }

    #[test]
    fn tuple_wrapped_conditionals_are_not_distributive() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const value: [never] extends [never] ? string : number = 'value';
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "value"), Ty::string());
    }

    #[test]
    fn naked_type_parameter_conditionals_distribute_over_substituted_unions() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare function f<T>(): T extends string ? boolean : number;
        const value = f<string | number>();
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value"),
            Ty::union(arena(&ret), [Ty::boolean(), Ty::number()])
        );
    }

    #[test]
    fn tuple_numeric_index_access_resolves_element_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        let t: [number, string];
        let t0 = t[0];
        let t1 = t[1];
        let t2 = t[2];
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "t0"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "t1"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "t2"), Ty::undefined());
    }

    #[test]
    fn contextually_typed_boolean_object_properties_keep_literal_location_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const plain = { huh: true };
        const annotated: { huh: boolean } = { huh: true };
        type StringsThenConfig = [...string[], { huh: boolean }];
        const tupleContext: StringsThenConfig = ['value', { huh: false }];
        ",
        );

        assert_eq!(
            get_object_property_types(&ret, "huh"),
            vec![Ty::boolean(), Ty::boolean_true(), Ty::boolean_false(),]
        );
    }

    #[test]
    fn const_initializers_use_literal_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        const count = 1;
        const label = "ready";
        const enabled = true;
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "count"),
            Ty::number_literal(arena(&ret), "1")
        );
        assert_eq!(
            get_global_symbol_type(&ret, "label"),
            Ty::string_literal(arena(&ret), "\"ready\"")
        );
        assert_eq!(get_global_symbol_type(&ret, "enabled"), Ty::boolean_true());
    }

    #[test]
    fn type_strings_render_string_literals_with_double_quotes() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);

        assert_eq!(
            Ty::string_literal(arena, "expects a string literal").to_type_string(),
            "\"expects a string literal\""
        );
    }

    #[test]
    fn literal_types_participate_in_widening_expressions() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        const count = 1;
        const sum = count + 2;
        const label = "ready";
        const message = label + "!";
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "sum"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "message"), Ty::string());
    }

    #[test]
    fn simple_inferred_variable_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        let l7 = false;
        let n = 23;
        let s = 'hello';
        let b = 1n;
        let a;
        let annotated: string = 23;
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "l7"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "n"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "s"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "b"), Ty::bigint());
        assert_eq!(get_global_symbol_type(&ret, "a"), Ty::any());
        assert_eq!(get_global_symbol_type(&ret, "annotated"), Ty::string());
    }

    #[test]
    fn angle_bracket_type_assertions_use_asserted_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const x: any;
        interface Box<T = number> { value: T; }
        interface SelfDefault<T = T> { value: T; }

        const xs = <string>x;
        const xu = <unknown>x;
        const xn = <number>x;
        const xa = <any>x;
        const boxed = (<Box>x);
        const boxedValue = (<Box>x).value;
        const explicitBoxedValue = (<Box<string>>x).value;
        const selfDefaultValue = (<SelfDefault>x).value;
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "xs"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "xu"), Ty::unknown());
        assert_eq!(get_global_symbol_type(&ret, "xn"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "xa"), Ty::any());
        assert_eq!(
            get_global_symbol_type(&ret, "boxed"),
            Ty::type_reference(arena(&ret), "Box", [Ty::number()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "boxed").to_type_string(),
            "Box<number>"
        );
        assert_eq!(get_global_symbol_type(&ret, "boxedValue"), Ty::number());
        assert_eq!(
            get_global_symbol_type(&ret, "explicitBoxedValue"),
            Ty::string()
        );
        assert_eq!(get_global_symbol_type(&ret, "selfDefaultValue"), Ty::any());
    }

    #[test]
    fn generic_function_infers_type_parameters_from_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function foo<T>(x: T) {
            return x;
        }

        const x = foo(123);
        const y = foo("test");
        const z = foo(true);
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "x"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "y"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "z"), Ty::boolean());
    }

    #[test]
    fn function_overloads_select_matching_signature() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function pick(x: string): string;
        function pick(x: number): number;
        function pick(x: string | number): string | number {
            return x;
        }

        const fromString = pick("ready");
        const fromNumber = pick(123);
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "fromString"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "fromNumber"), Ty::number());
    }

    #[test]
    fn function_overloads_skip_signatures_with_too_many_type_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function pick<T>(x: T): T;
        function pick<T, U>(x: T): U;
        function pick(x: unknown): unknown {
            return x;
        }

        const value = pick<number, string>(123);
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "value"), Ty::string());
    }

    #[test]
    fn interface_method_overloads_select_matching_signature() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface Picker {
            pick(x: string): string;
            pick(x: number): number;
        }

        declare const picker: Picker;
        const fromString = picker.pick("ready");
        const fromNumber = picker.pick(123);
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "fromString"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "fromNumber"), Ty::number());
    }

    #[test]
    fn single_interface_method_signature_location_uses_function_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface PredicateArray<T> {
            every<S extends T>(predicate: (value: T) => value is S): this is readonly S[];
        }
        "#,
        );

        assert_eq!(
            get_ts_method_signature_types(&ret, "every"),
            vec![
                "<S extends T>(predicate: (value: T) => value is S) => this is readonly S[]"
                    .to_string(),
            ]
        );
    }

    #[test]
    fn merged_interface_method_signature_locations_use_overload_object_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface MapLike<K> {
            delete(key: K): boolean;
        }
        interface MapLike<K> {
            delete(key: K): boolean;
        }
        "#,
        );

        assert_eq!(
            get_ts_method_signature_types(&ret, "delete"),
            vec![
                "{ (key: K): boolean; (key: K): boolean; }".to_string(),
                "{ (key: K): boolean; (key: K): boolean; }".to_string(),
            ]
        );
    }

    #[test]
    fn type_query_alias_instantiation_resolves_intersections() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        class ErrImpl<E> {
            e!: E;
        }

        declare const Err: typeof ErrImpl & (<T>() => T);
        type ErrAlias<U> = typeof Err<U>;
        declare const e: ErrAlias<number>;
        "#,
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "Err").to_type_string(),
            "typeof ErrImpl & (<T>() => T)"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "e"),
            Ty::intersection(
                arena,
                [
                    Ty::object(
                        arena,
                        [
                            Ty::property(
                                "new ()",
                                Ty::type_reference(arena, "ErrImpl", [Ty::number()]),
                            ),
                            Ty::property(
                                "prototype",
                                Ty::type_reference(arena, "ErrImpl", [Ty::any()]),
                            ),
                        ],
                    ),
                    Ty::function(arena, [], [], Ty::number()),
                ],
            )
        );
    }

    #[test]
    fn function_return_inference_visits_body_statements() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function empty() {
        }

        function onlyBareReturns(flag: boolean) {
            if (flag) {
                return;
            }
            return;
        }

        function nestedReturnExpression(flag: boolean) {
            if (flag) {
                return 1;
            }
        }

        function bareReturnBeforeExpression(flag: boolean) {
            if (flag) {
                return;
            }
            return "ready";
        }

        function literalUnion() {
            if (Math.random() > 0.5) {
                return 2;
            }
            return 1;
        }

        function ignoresNestedFunctionReturn() {
            function inner() {
                return true;
            }
        }

        const emptyResult = empty();
        const bareResult = onlyBareReturns(true);
        const nestedResult = nestedReturnExpression(true);
        const afterBareResult = bareReturnBeforeExpression(false);
        const literalUnionResult = literalUnion();
        const nestedFunctionResult = ignoresNestedFunctionReturn();
        "#,
        );
        let arena = arena(&ret);

        assert_eq!(get_global_symbol_type(&ret, "emptyResult"), Ty::void());
        assert_eq!(get_global_symbol_type(&ret, "bareResult"), Ty::void());
        assert_eq!(get_global_symbol_type(&ret, "nestedResult"), Ty::number());
        assert_eq!(
            get_global_symbol_type(&ret, "afterBareResult"),
            Ty::string()
        );
        assert_eq!(
            get_global_symbol_type(&ret, "literalUnionResult"),
            Ty::union(
                arena,
                [
                    Ty::number_literal(arena, "2"),
                    Ty::number_literal(arena, "1"),
                ],
            )
        );
        assert_eq!(
            get_global_symbol_type(&ret, "nestedFunctionResult"),
            Ty::void()
        );
    }

    #[test]
    fn expression_bodied_arrow_function_infers_return_expression() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "var predicate = () => false;");

        assert_eq!(
            get_global_symbol_type(&ret, "predicate").to_type_string(),
            "() => boolean"
        );
    }

    #[test]
    fn async_function_inference_wraps_return_type_in_promise() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        async function returnsString() {
            return 'value';
        }

        async function empty() {}

        const returnsNumber = async () => 1;
        const stringResult = returnsString();
        const emptyResult = empty();
        const numberResult = returnsNumber();
        "#,
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "returnsString").to_type_string(),
            "() => Promise<string>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "stringResult"),
            Ty::type_reference(arena, "Promise", [Ty::string()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "emptyResult"),
            Ty::type_reference(arena, "Promise", [Ty::void()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "numberResult"),
            Ty::type_reference(arena, "Promise", [Ty::number()])
        );
    }

    #[test]
    fn await_union_and_for_await_preserve_async_iterable_element_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        async function useStream<TQueryFnData>(
            streamFn: () => AsyncIterable<TQueryFnData> | Promise<AsyncIterable<TQueryFnData>>,
        ) {
            const stream = await streamFn();
            for await (const chunk of stream) {
                chunk;
            }
        }
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "stream").to_type_string(),
            "AsyncIterable<TQueryFnData>"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "chunk").to_type_string(),
            "Awaited<TQueryFnData>"
        );
    }

    #[test]
    fn await_structural_thenable_uses_fulfilled_callback_value_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function createPromiseLike(): PromiseLike<string>;

        interface MyThenable {
            then(onFulfilled: () => void, onRejected: () => void): MyThenable;
        }

        declare function createMyThenable(): MyThenable;

        async function main() {
            const promiseLikeValue = await createPromiseLike();
            const customThenableValue = await createMyThenable();
        }
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "promiseLikeValue"),
            Ty::string()
        );
        assert_eq!(
            get_first_symbol_type(&ret, "customThenableValue"),
            Ty::never()
        );
    }

    #[test]
    fn promise_constructor_contextually_types_executor_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "const promise = new Promise((resolve, reject) => resolve('value'));",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "promise"),
            Ty::type_reference(arena, "Promise", [Ty::unknown()])
        );
        assert_eq!(
            get_first_symbol_type(&ret, "resolve").to_type_string(),
            "(value: unknown) => void"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "reject").to_type_string(),
            "(reason?: any) => void"
        );
    }

    #[test]
    fn promise_finally_returns_original_promise_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "const rejected = Promise.reject('value').finally();",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "rejected"),
            Ty::type_reference(arena(&ret), "Promise", [Ty::never()])
        );
    }

    #[test]
    fn promise_then_and_catch_infer_callback_returns_through_nullable_callback_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        async function returnsPromise() { return 'value'; }
        const thenMethod = returnsPromise().then;
        const thenResult = returnsPromise().then(() => {});
        const defaultThenResult = returnsPromise().then();
        const catchMethod = Promise.reject('value').catch;
        const catchResult = Promise.reject('value').catch(() => {});
        "#,
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "thenMethod").to_type_string(),
            "<TResult1, TResult2>(onfulfilled?: ((value: string) => TResult1 | PromiseLike<TResult1>) | null | undefined, onrejected?: ((reason: any) => TResult2 | PromiseLike<TResult2>) | null | undefined) => Promise<TResult1 | TResult2>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "thenResult"),
            Ty::type_reference(arena, "Promise", [Ty::void()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "defaultThenResult"),
            Ty::type_reference(arena, "Promise", [Ty::string()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "catchMethod").to_type_string(),
            "<TResult>(onrejected?: ((reason: any) => TResult | PromiseLike<TResult>) | null | undefined) => Promise<TResult>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "catchResult"),
            Ty::type_reference(arena, "Promise", [Ty::void()])
        );
    }

    #[test]
    fn awaited_special_handling_requires_global_awaited_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type Awaited<T> = { value: T };
        type Value = Awaited<Promise<number>>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Value").to_type_string(),
            "{ value: Promise<number>; }"
        );
    }

    #[test]
    fn global_script_function_declarations_merge_across_programs() {
        let allocator = Allocator::default();
        let host = TestProgramHost::new("/project")
            .add_file(
                "/project/a.ts",
                "async function returnsPromise() { return 'value'; }",
            )
            .add_file(
                "/project/b.ts",
                "async function returnsPromise() { return 'value'; }",
            )
            .add_file(
                "/project/e.ts",
                "async function returnsPromise() { return 'value'; }",
            );
        let store = program::ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/a.ts")
            .add_root_file("/project/b.ts")
            .add_root_file("/project/e.ts")
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/a.ts")).unwrap();
        let ret = ParseAndCheck { store, program_id };

        assert_eq!(
            get_global_symbol_type(&ret, "returnsPromise").to_type_string(),
            "{ (): Promise<string>; (): Promise<string>; (): Promise<string>; }"
        );
    }

    #[test]
    fn generic_function_uses_explicit_type_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function foo<T>(x: T) {
            return x;
        }

        const x = foo<string>("test");
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "x"), Ty::string());
    }

    #[test]
    fn generic_function_substitutes_object_return_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function box<T>(x: T) {
            return {value: x};
        }

        const x = box(123);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "x"),
            Ty::object(arena(&ret), [Ty::property("value", Ty::number())])
        );
    }

    #[test]
    fn generic_type_references_preserve_type_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type Box<T> = { value: T };

        function box<T>(x: T): Box<T> {
            return {value: x};
        }

        const explicit: Box<string> = {value: "test"};
        const inferred = box(123);
        const fromExplicitCall = box<string>("test");
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "explicit"),
            Ty::type_reference(arena(&ret), "Box", [Ty::string()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "inferred"),
            Ty::type_reference(arena(&ret), "Box", [Ty::number()])
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromExplicitCall"),
            Ty::type_reference(arena(&ret), "Box", [Ty::string()])
        );
    }

    #[test]
    fn generic_function_defaults_render_and_apply_when_not_inferred() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface A { a: number; }
        declare const a: A;
        declare const fn: <T = A>(x: T) => T;
        declare function foo<T = A>(x?: T): T;

        const fromDefault = foo();
        const fromInference = foo(a);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "fn").to_type_string(),
            "<T = A>(x: T) => T"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(),
            "<T = A>(x?: T) => T"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromDefault"),
            Ty::type_reference(arena(&ret), "A", std::iter::empty())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromInference"),
            Ty::type_reference(arena(&ret), "A", std::iter::empty())
        );
    }

    #[test]
    fn generic_function_constraints_render_and_apply_when_not_inferred() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface A { a: number; }
        declare const a: A;
        declare const fn: <T extends A>(x: T) => T;
        declare function foo<T extends A, U extends T = T>(x?: T, y?: U): [T, U];

        const fromConstraint = foo();
        const fromInference = foo(a);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "fn").to_type_string(),
            "<T extends A>(x: T) => T"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(),
            "<T extends A, U extends T = T>(x?: T, y?: U) => [T, U]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromConstraint").to_type_string(),
            "[A, A]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromInference").to_type_string(),
            "[A, A]"
        );
    }

    #[test]
    fn keyof_constraints_and_indexed_access_types_render() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface Window {}
        interface WindowEventMap {}
        declare const source: {
            <K extends keyof WindowEventMap>(type: K, listener: (this: Window, ev: WindowEventMap[K]) => any): void;
        };
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "source").to_type_string(),
            "{ <K extends keyof WindowEventMap>(type: K, listener: (this: Window, ev: WindowEventMap[K]) => any): void; }"
        );
    }

    #[test]
    fn new_expression_infers_class_instance_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        class Foo {
            doThing(x: {a: number}) {
                return {b: x.a};
            }
        }
        const c = new Foo();
        const x = c.doThing({a: 12});
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "c"),
            Ty::type_reference(arena(&ret), "Foo", std::iter::empty())
        );
        assert_eq!(
            get_global_symbol_type(&ret, "x"),
            Ty::object(arena(&ret), [Ty::property("b", Ty::number())])
        );
    }

    #[test]
    fn class_properties_are_available_on_instances_statics_and_this() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        class Item {
            name: string = "item";
        }

        class Example {
            ready: boolean = false;
            count = 1;
            item: Item = new Item();
            static enabled: boolean = true;

            getReady() {
                return this.ready;
            }

            getCount() {
                return this.count;
            }

            getItemName() {
                return this.item.name;
            }

            static getEnabled() {
                return Example.enabled;
            }
        }

        const instance = new Example();
        const ready = instance.ready;
        const count = instance.count;
        const itemName = instance.item.name;
        const readyFromThis = instance.getReady();
        const countFromThis = instance.getCount();
        const nameFromThis = instance.getItemName();
        const enabled = Example.enabled;
        const enabledFromMethod = Example.getEnabled();
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "ready"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "count"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "itemName"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "readyFromThis"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "countFromThis"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "nameFromThis"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "enabled"), Ty::boolean());
        assert_eq!(
            get_global_symbol_type(&ret, "enabledFromMethod"),
            Ty::boolean()
        );
    }

    #[test]
    fn array_every_contextually_types_callback_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        class Ship {
            isSunk: boolean = false;
        }

        class Board {
            ships: Ship[] = [];

            allShipsSunk() {
                return this.ships.every(function (val) {
                    return val.isSunk;
                });
            }
        }

        const board = new Board();
        const sunk = board.allShipsSunk();
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "val"),
            Ty::type_reference(arena(&ret), "Ship", std::iter::empty())
        );
        assert_eq!(get_global_symbol_type(&ret, "sunk"), Ty::boolean());
    }

    #[test]
    fn array_map_infers_async_callback_return_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const mapped = [1, 2, 3].map(async x => x + 1);
        ",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_global_symbol_type(&ret, "mapped"),
            Ty::array(arena, Ty::type_reference(arena, "Promise", [Ty::number()]))
        );
        assert_eq!(get_first_symbol_type(&ret, "x"), Ty::number());
    }

    #[test]
    fn array_map_string_callback_member_uses_global_string_interface() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const lengths = ['a', 'bb', 'ccc'].map(x => x.length);
        ",
        );
        let arena = arena(&ret);

        assert_eq!(get_first_symbol_type(&ret, "x"), Ty::string());
        assert_eq!(
            get_static_member_expression_types(&ret, "length"),
            vec![Ty::number()]
        );
        assert_eq!(
            get_global_symbol_type(&ret, "lengths"),
            Ty::array(arena, Ty::number())
        );
    }

    #[test]
    fn primitive_and_object_members_use_global_interfaces() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const key: symbol;
        declare const big: bigint;
        const objectText = ({ a: 1 }).toString();
        const functionLength = ((value: number) => value).length;
        const fixed = (1).toFixed();
        const boolValue = (true).valueOf();
        const symbolText = key.toString();
        const bigValue = big.valueOf();
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "objectText"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "functionLength"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "fixed"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "boolValue"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "symbolText"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "bigValue"), Ty::bigint());
    }

    #[test]
    fn function_parameter_declared_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "function foo(a: number, b: string, c: boolean) {}",
        );

        assert_eq!(get_symbol_type_in_function(&ret, "foo", "a"), Ty::number());
        assert_eq!(get_symbol_type_in_function(&ret, "foo", "b"), Ty::string());
        assert_eq!(get_symbol_type_in_function(&ret, "foo", "c"), Ty::boolean());
    }

    #[test]
    fn optional_function_parameters_render_optional_in_signatures() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "declare function foo(a?: number): number;");

        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(),
            "(a?: number) => number"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "foo", "a"),
            Ty::union(arena(&ret), [Ty::number(), Ty::undefined()])
        );
    }

    #[test]
    fn rest_function_parameters_render_in_signatures() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "function foo(a: string, b?: string, c?: number, ...d: number[]) {}",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(),
            "(a: string, b?: string, c?: number, ...d: number[]) => void"
        );
        let Ty::Function(function) = get_global_symbol_type(&ret, "foo") else {
            panic!("expected function type");
        };
        let rest_parameter = function.parameters[3];
        assert_eq!(rest_parameter.name, "d");
        assert!(rest_parameter.rest);
    }

    #[test]
    fn function_type_annotations_resolve_to_function_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "declare function pipe<A extends any[], B>(ab: (...args: A) => B): B;",
        );
        let arena = arena(&ret);

        assert_eq!(
            get_first_symbol_type(&ret, "ab"),
            Ty::function(
                arena,
                [],
                [Ty::rest_parameter(
                    arena.str("args"),
                    Ty::type_reference(arena, arena.str("A"), []),
                )],
                Ty::type_reference(arena, arena.str("B"), []),
            )
        );
    }

    #[test]
    fn function_type_predicates_render_in_signatures() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
declare function acceptsPredicate<T, S extends T>(
    predicate: (value: T) => value is S,
    assertion: (value: unknown) => asserts value is string,
): void;
"#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "predicate").to_type_string(),
            "(value: T) => value is S"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "assertion").to_type_string(),
            "(value: unknown) => asserts value is string"
        );
    }

    #[test]
    fn test_get_global_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "");
        let checker = CheckerBuilder::new().build(&ret.store);

        // Now test things that should be in the global environment:
        assert_eq!(
            get_global_type(&ret, ret.program_id, "Promise"),
            Ty::type_reference(arena(&ret), "Promise", std::iter::empty())
        );
        assert_eq!(
            checker.get_global_promise_type(ret.program_id),
            Ty::type_reference(arena(&ret), "Promise", std::iter::empty())
        );
    }
}
