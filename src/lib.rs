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

fn is_promise_like_type_reference(name: &str) -> bool {
    matches!(name, "Promise" | "PromiseLike")
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
    use crate::checker::{Checker, CheckerBuilder, CheckerReturn, NodeRef, SymbolRef};
    use crate::checker_impl::UNDEFINED_IDENT;
    use crate::mapper::TypeMapper;
    use crate::program::ProgramHost;
    use oxc_allocator::Allocator;
    use oxc_ast::ast::NumberBase;
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
        arena: CheckerArena<'a>,
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
        let arena = CheckerArena::new(store.allocator());
        ParseAndCheck {
            store,
            program_id,
            arena,
        }
    }

    fn checker<'a, 'store>(ret: &'store ParseAndCheck<'a>) -> CheckerReturn<'a, 'store> {
        CheckerBuilder::new().build_with_arena(&ret.store, ret.arena)
    }

    fn get_global_symbol_type<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Ty<'a> {
        let checker = checker(ret);
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
        let checker = checker(ret);
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

    #[test]
    fn constrained_type_at_location() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "function negate<T extends number>(value: T) { return -value; }",
        );
        let type_checker = checker(&ret);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let value_node = semantic
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| match node.kind() {
                AstKind::IdentifierReference(identifier) if identifier.name == "value" => {
                    Some(NodeRef::new(ret.program_id, node_id))
                }
                _ => None,
            })
            .unwrap();

        assert_eq!(
            type_checker.get_constrained_type_at_location(value_node),
            Ty::number()
        );

        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "function negate<T>(value: T) { return -value; }",
        );
        let type_checker = checker(&ret);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let value_node = semantic
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| match node.kind() {
                AstKind::IdentifierReference(identifier) if identifier.name == "value" => {
                    Some(NodeRef::new(ret.program_id, node_id))
                }
                _ => None,
            })
            .unwrap();

        assert_ne!(
            type_checker.get_constrained_type_at_location(value_node),
            Ty::number()
        );
    }

    fn get_symbol_type_in_function<'a>(
        ret: &ParseAndCheck<'a>,
        func_name: &str,
        param_name: &str,
    ) -> Ty<'a> {
        let checker = checker(ret);
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
        let checker = checker(ret);
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
    ) -> Option<Ty<'a>> {
        let checker = checker(ret);
        checker.get_global_type_reference(program_id, name, std::iter::empty())
    }

    fn get_object_property_types<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Vec<Ty<'a>> {
        let checker = checker(ret);
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
        let checker = checker(ret);
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
                            .to_type_string(ret.arena),
                    )
                }
                _ => None,
            })
            .collect()
    }

    fn get_ts_property_signature_types(ret: &ParseAndCheck<'_>, name: &str) -> Vec<String> {
        let checker = checker(ret);
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
                            .to_type_string(ret.arena),
                    )
                }
                _ => None,
            })
            .collect()
    }

    fn get_identifier_reference_types<'a>(ret: &ParseAndCheck<'a>, name: &str) -> Vec<Ty<'a>> {
        let checker = checker(ret);
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
        let checker = checker(ret);
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
        ret.arena
    }

    trait TestTypeIdentity<'a> {
        fn is_identical_to(&self, other: &Self, arena: CheckerArena<'a>) -> bool;
    }

    impl<'a> TestTypeIdentity<'a> for Ty<'a> {
        fn is_identical_to(&self, other: &Self, arena: CheckerArena<'a>) -> bool {
            arena.is_type_identical_to(*self, *other)
        }
    }

    impl<'a> TestTypeIdentity<'a> for Option<Ty<'a>> {
        fn is_identical_to(&self, other: &Self, arena: CheckerArena<'a>) -> bool {
            match (*self, *other) {
                (Some(left), Some(right)) => arena.is_type_identical_to(left, right),
                (None, None) => true,
                _ => false,
            }
        }
    }

    impl<'a> TestTypeIdentity<'a> for Vec<Ty<'a>> {
        fn is_identical_to(&self, other: &Self, arena: CheckerArena<'a>) -> bool {
            self.len() == other.len()
                && self
                    .iter()
                    .zip(other)
                    .all(|(left, right)| arena.is_type_identical_to(*left, *right))
        }
    }

    fn assert_type_eq<'a, T>(arena: CheckerArena<'a>, left: T, right: T)
    where
        T: TestTypeIdentity<'a> + std::fmt::Debug,
    {
        assert!(
            left.is_identical_to(&right, arena),
            "type structures differ\n  left: {left:?}\n right: {right:?}"
        );
    }

    fn contains_type<'a>(arena: CheckerArena<'a>, types: &[Ty<'a>], expected: Ty<'a>) -> bool {
        types
            .iter()
            .any(|ty| arena.is_type_identical_to(*ty, expected))
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
    fn checker_enumerates_registered_types_by_id() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const values = [1, 2];");
        let checker = checker(&ret);
        let symbol_id = ret
            .store
            .entry(ret.program_id)
            .unwrap()
            .semantic()
            .scoping()
            .get_root_binding(Ident::from("values"))
            .unwrap();
        let initial_count = checker.type_count();
        let ty = checker.get_type_of_symbol(SymbolRef::new(ret.program_id, symbol_id));

        assert!(checker.type_count() > initial_count);
        let ids = checker.type_ids().collect::<Vec<_>>();
        assert_eq!(ids.len(), checker.type_count());
        assert!(
            ids.iter()
                .enumerate()
                .all(|(index, id)| id.get() == u32::try_from(index + 1).unwrap())
        );
        assert_eq!(checker.types().map(Ty::id).collect::<Vec<_>>(), ids);
        assert_eq!(checker.type_from_id(ty.id()), Some(ty));

        let mut by_id = HashMap::new();
        by_id.insert(ty.id(), "values");
        assert_eq!(by_id.get(&ty.id()), Some(&"values"));
    }

    #[test]
    fn default_lib_provides_global_type_symbols() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const x = 1;");
        let checker = checker(&ret);

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
                checker
                    .get_type_of_symbol(value_symbol)
                    .to_type_string(checker.arena),
                constructor_type
            );
        }
    }

    #[test]
    #[expect(clippy::expect_used)]
    fn type_alias_binding_location_uses_type_meaning_for_merged_symbol() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            type NodeFilter = ((value: string) => number) | { accept(value: string): number };
            declare var NodeFilter: { readonly VALUE: 1 };
            const nodeFilterValue = NodeFilter;
            ",
        );
        let checker = checker(&ret);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let alias_name_node = semantic
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| match node.kind() {
                AstKind::BindingIdentifier(identifier)
                    if identifier.name == Ident::from("NodeFilter")
                        && matches!(
                            semantic.nodes().parent_kind(node_id),
                            AstKind::TSTypeAliasDeclaration(_)
                        ) =>
                {
                    Some(node_id)
                }
                _ => None,
            })
            .expect("expected type alias binding identifier");

        assert_eq!(
            checker
                .get_type_at_location(NodeRef::new(ret.program_id, alias_name_node))
                .to_type_string(ret.arena),
            "((value: string) => number) | { accept(value: string): number; }"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "nodeFilterValue").to_type_string(ret.arena),
            "{ readonly VALUE: 1; }"
        );
    }

    #[test]
    fn duplicate_class_declaration_value_types_are_location_specific() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            class C<T = number> {}
            class D extends C {}
            class D extends C<string> {}
            export {};
            ",
        );
        let checker = checker(&ret);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let types = semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| {
                let AstKind::BindingIdentifier(identifier) = node.kind() else {
                    return None;
                };
                if identifier.name != Ident::from("D")
                    || !matches!(semantic.nodes().parent_kind(node_id), AstKind::Class(_))
                {
                    return None;
                }
                Some(
                    checker
                        .get_type_at_location(NodeRef::new(ret.program_id, node_id))
                        .to_type_string(ret.arena),
                )
            })
            .collect::<Vec<_>>();

        assert_eq!(types, vec!["typeof D", "{ new <string>(): {}; }"]);
    }

    #[test]
    #[expect(clippy::expect_used)]
    fn checker_renders_transparent_default_lib_type_aliases() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "const value: Base64URLString[] = []; interface Shape { method(value: Base64URLString): Base64URLString; }",
        );
        let checker = checker(&ret);
        let alias_symbol = checker
            .get_type_symbol_for_name(ret.program_id, "Base64URLString")
            .expect("expected Base64URLString from the default library");
        assert!(checker.entry(alias_symbol.program_id).is_lib());
        let alias_declaration = checker
            .semantic(alias_symbol.program_id)
            .scoping()
            .symbol_declaration(alias_symbol.symbol_id);
        assert!(matches!(
            checker.node_kind(NodeRef::new(alias_symbol.program_id, alias_declaration)),
            AstKind::TSTypeAliasDeclaration(_) | AstKind::BindingIdentifier(_)
        ));
        let node_id = ret
            .store
            .entry(ret.program_id)
            .unwrap()
            .semantic()
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(
                    node.kind(),
                    AstKind::BindingIdentifier(identifier) if identifier.name == Ident::from("value")
                )
                .then_some(node_id)
            })
            .unwrap();
        let node = NodeRef::new(ret.program_id, node_id);
        let ty = checker.get_type_at_location(node);
        let TypeData::Array(array) = checker.arena.type_data(ty) else {
            panic!("expected an array type");
        };
        let method_node_id = ret
            .store
            .entry(ret.program_id)
            .unwrap()
            .semantic()
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(node.kind(), AstKind::TSMethodSignature(_)).then_some(node_id)
            })
            .unwrap();
        let method_node = NodeRef::new(ret.program_id, method_node_id);
        let method_type = checker.get_type_at_location(method_node);

        assert!(checker.type_alias_metadata(array.element_type).is_some());
        assert_eq!(ty.to_type_string(checker.arena), "Base64URLString[]");
        assert_eq!(checker.type_to_string(ty, node), "string[]");
        assert_eq!(
            checker.type_to_string(method_type, method_node),
            "(value: Base64URLString) => Base64URLString"
        );
    }

    #[test]
    fn checker_renders_default_lib_named_aliases_in_structural_positions() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "interface Shape { property: WindowProxy; method(value: WindowProxy): void; }",
        );
        let checker = checker(&ret);
        let nodes = ret.store.entry(ret.program_id).unwrap().semantic().nodes();
        let property_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(node.kind(), AstKind::TSPropertySignature(_)).then_some(node_id)
            })
            .unwrap();
        let method_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(node.kind(), AstKind::TSMethodSignature(_)).then_some(node_id)
            })
            .unwrap();
        let parameter_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(node.kind(), AstKind::FormalParameter(_)).then_some(node_id)
            })
            .unwrap();
        let parameter_binding_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(
                    node.kind(),
                    AstKind::BindingIdentifier(identifier)
                        if identifier.name == Ident::from("value")
                )
                .then_some(node_id)
            })
            .unwrap();

        assert_eq!(
            checker.type_to_string(
                checker.get_type_at_location(NodeRef::new(ret.program_id, property_node_id)),
                NodeRef::new(ret.program_id, property_node_id),
            ),
            "Window"
        );
        assert_eq!(
            checker.type_to_string(
                checker.get_type_at_location(NodeRef::new(ret.program_id, parameter_node_id)),
                NodeRef::new(ret.program_id, parameter_node_id),
            ),
            "Window"
        );
        assert_eq!(
            checker.type_to_string(
                checker
                    .get_type_at_location(NodeRef::new(ret.program_id, parameter_binding_node_id,)),
                NodeRef::new(ret.program_id, parameter_binding_node_id),
            ),
            "Window"
        );
        assert_eq!(
            checker.type_to_string(
                checker.get_type_at_location(NodeRef::new(ret.program_id, method_node_id)),
                NodeRef::new(ret.program_id, method_node_id),
            ),
            "(value: WindowProxy) => void"
        );

        let dom_program_id = ret.store.id_for_path(Path::new("lib.dom.d.ts")).unwrap();
        let dom_nodes = ret.store.entry(dom_program_id).unwrap().semantic().nodes();
        let dom_parameter_node_id = dom_nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(
                    node.kind(),
                    AstKind::BindingIdentifier(identifier)
                        if identifier.name == Ident::from("viewArg")
                )
                .then_some(node_id)
            })
            .unwrap();
        let dom_parameter_node = NodeRef::new(dom_program_id, dom_parameter_node_id);
        assert_eq!(
            checker.type_to_string(
                checker.get_type_at_location(dom_parameter_node),
                dom_parameter_node,
            ),
            "Window | null | undefined"
        );
    }

    #[test]
    fn checker_resolves_interface_heritage_value_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "interface DOMException extends Error {}");
        let checker = checker(&ret);
        let nodes = ret.store.entry(ret.program_id).unwrap().semantic().nodes();
        let heritage_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(node.kind(), AstKind::TSInterfaceHeritage(_)).then_some(node_id)
            })
            .unwrap();
        let heritage_node = NodeRef::new(ret.program_id, heritage_node_id);

        assert_eq!(
            checker.type_to_string(checker.get_type_at_location(heritage_node), heritage_node,),
            "ErrorConstructor"
        );
    }

    #[test]
    fn checker_expands_object_type_queries_at_variable_bindings() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "declare const Target: { new (): Target; prototype: Target; }; declare const Alias: typeof Target;",
        );
        let checker = checker(&ret);
        let nodes = ret.store.entry(ret.program_id).unwrap().semantic().nodes();
        let alias_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(
                    node.kind(),
                    AstKind::BindingIdentifier(identifier) if identifier.name == Ident::from("Alias")
                )
                .then_some(node_id)
            })
            .unwrap();
        let alias_node = NodeRef::new(ret.program_id, alias_node_id);

        assert_eq!(
            checker.type_to_string(checker.get_type_at_location(alias_node), alias_node),
            "{ new (): Target; prototype: Target; }"
        );
    }

    #[test]
    fn checker_merges_standard_library_namespace_function_declarations() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "declare namespace CSS { function Hz(value: number): CSSUnitValue; }",
        );
        let checker = checker(&ret);
        let nodes = ret.store.entry(ret.program_id).unwrap().semantic().nodes();
        let hz_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(
                    node.kind(),
                    AstKind::BindingIdentifier(identifier) if identifier.name == Ident::from("Hz")
                )
                .then_some(node_id)
            })
            .unwrap();
        let hz_node = NodeRef::new(ret.program_id, hz_node_id);

        assert_eq!(
            checker.type_to_string(checker.get_type_at_location(hz_node), hz_node),
            "{ (value: number): CSSUnitValue; (value: number): CSSUnitValue; }"
        );
    }

    #[test]
    fn checker_expands_global_exclude_in_method_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "interface Shape { method(format: Exclude<KeyFormat, \"jwk\">): void; }",
        );
        let checker = checker(&ret);
        let nodes = ret.store.entry(ret.program_id).unwrap().semantic().nodes();
        let format_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(
                    node.kind(),
                    AstKind::BindingIdentifier(identifier)
                        if identifier.name == Ident::from("format")
                )
                .then_some(node_id)
            })
            .unwrap();
        let format_node = NodeRef::new(ret.program_id, format_node_id);

        assert_eq!(
            checker.type_to_string(checker.get_type_at_location(format_node), format_node),
            "\"pkcs8\" | \"raw\" | \"spki\""
        );
    }

    #[test]
    fn checker_renders_transparent_local_type_aliases_by_display_context() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "type Text = string; interface Shape { property: Text; } const value: Text = \"\";",
        );
        let checker = checker(&ret);
        let nodes = ret.store.entry(ret.program_id).unwrap().semantic().nodes();
        let property_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(node.kind(), AstKind::TSPropertySignature(_)).then_some(node_id)
            })
            .unwrap();
        let value_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(
                    node.kind(),
                    AstKind::BindingIdentifier(identifier) if identifier.name == Ident::from("value")
                )
                .then_some(node_id)
            })
            .unwrap();
        let property_node = NodeRef::new(ret.program_id, property_node_id);
        let value_node = NodeRef::new(ret.program_id, value_node_id);
        let property_type = checker.get_type_at_location(property_node);
        let value_type = checker.get_type_at_location(value_node);

        assert_eq!(
            checker.type_to_string(property_type, property_node),
            "string"
        );
        assert_eq!(checker.type_to_string(value_type, value_node), "Text");
    }

    #[test]
    fn checker_renders_transparent_aliases_in_type_alias_context() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "type ArrayKey = number; type Path = `${ArrayKey}`;",
        );
        let checker = checker(&ret);
        let nodes = ret.store.entry(ret.program_id).unwrap().semantic().nodes();
        let path_node_id = nodes
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(
                    node.kind(),
                    AstKind::BindingIdentifier(identifier)
                        if identifier.name == Ident::from("Path")
                            && matches!(
                                nodes.parent_kind(node_id),
                                AstKind::TSTypeAliasDeclaration(_)
                            )
                )
                .then_some(node_id)
            })
            .unwrap();
        let path_node = NodeRef::new(ret.program_id, path_node_id);

        assert_eq!(
            checker.type_to_string(checker.get_type_at_location(path_node), path_node),
            "`${number}`"
        );
    }

    #[test]
    fn checker_renders_alias_chains_to_named_unions() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "interface Shape { hash: HashWrapper; } interface HashAlgorithm {} type HashTarget = HashAlgorithm | string; type HashWrapper = HashTarget;",
        );
        let checker = checker(&ret);
        let hash_node_id = ret
            .store
            .entry(ret.program_id)
            .unwrap()
            .semantic()
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(node.kind(), AstKind::TSPropertySignature(_)).then_some(node_id)
            })
            .unwrap();
        let hash_node = NodeRef::new(ret.program_id, hash_node_id);
        let hash_type = checker.get_type_at_location(hash_node);

        assert_eq!(checker.type_to_string(hash_type, hash_node), "HashTarget");
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
    fn checker_preserves_named_alias_chains_for_formal_parameters() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "type Lazy<T, R> = () => R; type Pred<T> = Lazy<T, boolean>; declare function filter<T>(predicate: Pred<T>): void;",
        );
        let checker = checker(&ret);
        let parameter_node_id = ret
            .store
            .entry(ret.program_id)
            .unwrap()
            .semantic()
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| {
                matches!(node.kind(), AstKind::FormalParameter(_)).then_some(node_id)
            })
            .unwrap();
        let parameter_node = NodeRef::new(ret.program_id, parameter_node_id);
        let parameter_type = checker.get_type_at_location(parameter_node);

        assert_eq!(
            checker.type_to_string(parameter_type, parameter_node),
            "Pred<T>"
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
                .to_type_string(checker.arena),
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

        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "value"),
            Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal),
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

        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "value"),
            Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal),
        );
        assert_type_eq(
            arena,
            get_identifier_reference_types(&ret, "undefined"),
            vec![Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal)],
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

        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "arrayCtor"),
            Ty::type_reference(arena, "ArrayConstructor", []),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "promiseCtor"),
            Ty::type_reference(arena, "PromiseConstructor", []),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "mapCtor"),
            Ty::type_reference(arena, "MapConstructor", []),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "setCtor"),
            Ty::type_reference(arena, "SetConstructor", []),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "symbolCtor"),
            Ty::type_reference(arena, "SymbolConstructor", []),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "objectCtor"),
            Ty::type_reference(arena, "ObjectConstructor", []),
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

        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "keys"),
            Ty::array(arena, Ty::string()),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "values"),
            Ty::array(arena, Ty::number()),
        );
    }

    #[test]
    fn window_and_global_this_expose_global_function_overloads() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            const bare = postMessage;
            const global = globalThis.postMessage;
            const windowPost = window.postMessage;
            ",
        );
        let type_strings = get_static_member_expression_types(&ret, "postMessage")
            .into_iter()
            .map(|ty| ty.to_type_string(ret.arena))
            .collect::<Vec<_>>();
        let expected = "{ (message: any, targetOrigin: string, transfer?: Transferable[]): void; (message: any, options?: WindowPostMessageOptions): void; }";

        assert_eq!(
            get_global_symbol_type(&ret, "bare").to_type_string(ret.arena),
            expected
        );
        assert_eq!(
            type_strings,
            vec![expected.to_string(), format!("{expected} & {expected}")]
        );
    }

    #[test]
    fn global_this_exposes_script_var_but_not_lexical_bindings() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            var objectProperty = 1;
            let lexicalBinding = \"hidden\";
            const direct = globalThis.objectProperty;
            const computed = globalThis[\"objectProperty\"];
            const excluded = globalThis.lexicalBinding;
            const selfReference = globalThis.globalThis;
            type GlobalKeys = keyof typeof globalThis;
            type HasObjectProperty = \"objectProperty\" extends keyof typeof globalThis ? true : false;
            type IndexedObjectProperty = (typeof globalThis)[\"objectProperty\"];
            type MappedGlobals = { [Key in keyof typeof globalThis]: (typeof globalThis)[Key] };
            type MappedObjectProperty = MappedGlobals[\"objectProperty\"];
            type MappedSelfReference = MappedGlobals[\"globalThis\"];
            ",
        );
        let arena = arena(&ret);

        assert_type_eq(arena, get_global_symbol_type(&ret, "direct"), Ty::number());
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "computed"),
            Ty::number(),
        );
        let excluded = get_global_symbol_type(&ret, "excluded");
        assert_eq!(
            excluded.error_kind(arena),
            Some(TypeErrorKind::UnresolvedMember)
        );
        assert_eq!(excluded.to_type_string(arena), "any");
        assert_eq!(
            get_global_symbol_type(&ret, "selfReference").to_type_string(arena),
            "typeof globalThis",
        );
        assert_eq!(
            get_type_alias_type(&ret, "GlobalKeys").to_type_string(arena),
            "keyof typeof globalThis",
        );
        assert_type_eq(
            arena,
            get_type_alias_type(&ret, "HasObjectProperty"),
            Ty::boolean_true(),
        );
        assert_type_eq(
            arena,
            get_type_alias_type(&ret, "IndexedObjectProperty"),
            Ty::number(),
        );
        assert_type_eq(
            arena,
            get_type_alias_type(&ret, "MappedObjectProperty"),
            Ty::number(),
        );
        assert_eq!(
            get_type_alias_type(&ret, "MappedSelfReference").to_type_string(arena),
            "typeof globalThis",
        );

        let global_this = get_global_symbol_type(&ret, "selfReference");
        let checker = checker(&ret);
        assert!(checker.is_assignable_to(
            global_this,
            Ty::object(
                arena,
                [Ty::property(arena.str("objectProperty"), Ty::number())],
            ),
        ));
        assert!(!checker.is_assignable_to(
            global_this,
            Ty::object(
                arena,
                [Ty::property(arena.str("lexicalBinding"), Ty::string())],
            ),
        ));
    }

    #[test]
    fn global_this_excludes_module_scoped_variables() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            export {};
            var moduleScoped = 1;
            const leaked = globalThis.moduleScoped;
            ",
        );

        let leaked = get_global_symbol_type(&ret, "leaked");
        assert_eq!(
            leaked.error_kind(ret.arena),
            Some(TypeErrorKind::UnresolvedMember)
        );
        assert_eq!(leaked.to_type_string(ret.arena), "any");
    }

    #[test]
    fn callable_types_expose_function_and_object_members() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        function declared(value: string) { return value; }

        const arrowLocale = (() => {}).toLocaleString();
        const declaredLocale = declared.toLocaleString();
        const declaredLength = declared.length;
        const arrowHasOwn = (() => {}).hasOwnProperty('call');
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "arrowLocale"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "declaredLocale"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "declaredLength"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "arrowHasOwn"), Ty::boolean());
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
        let checker = checker(&ret);
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
            checker
                .get_type_of_symbol(symbol)
                .to_type_string(checker.arena)
        };

        assert_eq!(type_reference_type("Array"), "ArrayConstructor");
        assert_eq!(type_reference_type("Promise"), "PromiseConstructor");
    }

    #[test]
    fn enum_member_types_are_canonical_across_locations() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            enum E { A, B }
            const value = E.A;
            type Members = E.A | E.A | E.B;
            ",
        );
        let checker = checker(&ret);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();

        let declaration_type = semantic
            .nodes()
            .iter_enumerated()
            .find_map(|(node_id, node)| match node.kind() {
                AstKind::TSEnumMember(member) if member.id.static_name().as_str() == "A" => {
                    Some(checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)))
                }
                _ => None,
            })
            .unwrap();
        let value_type = get_global_symbol_type(&ret, "value");
        let members_type = get_type_alias_type(&ret, "Members");

        assert_eq!(declaration_type, value_type);
        assert!(matches!(
            ret.arena.type_data(declaration_type),
            types::TypeData::TypeReference(reference) if reference.target.is_some()
        ));
        let types::TypeData::Union(union) = ret.arena.type_data(members_type) else {
            panic!("expected enum member union");
        };
        assert_eq!(union.types.len(), 2);
        assert_eq!(union.types[0], declaration_type);
        assert_eq!(
            union
                .types
                .iter()
                .map(|ty| ty.to_type_string(ret.arena))
                .collect::<Vec<_>>(),
            ["E.A", "E.B"]
        );
    }

    #[test]
    fn same_named_enum_members_in_different_scopes_are_distinct() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            function first() {
                enum E { A }
                return E.A;
            }
            function second() {
                enum E { A }
                return E.A;
            }
            ",
        );

        let member_types = get_static_member_expression_types(&ret, "A");
        assert_eq!(member_types.len(), 2);
        assert_ne!(member_types[0], member_types[1]);
        assert_eq!(member_types[0].to_type_string(ret.arena), "E.A");
        assert_eq!(member_types[1].to_type_string(ret.arena), "E.A");
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
        assert_eq!(lib_count, crate::global_lib::default_lib_files().len());

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
        assert_type_eq(
            ret.arena,
            reference_types[0],
            Ty::union(arena(&ret), [Ty::string(), Ty::undefined()]),
        );
        assert_eq!(reference_types[1], Ty::string());
        assert_type_eq(
            ret.arena,
            reference_types[2],
            Ty::union(arena(&ret), [Ty::string(), Ty::undefined()]),
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
        assert_type_eq(
            ret.arena,
            reference_types[0],
            Ty::union(arena(&ret), [Ty::string(), Ty::number(), Ty::boolean()]),
        );
        assert_eq!(reference_types[1], Ty::string());
        assert_type_eq(
            ret.arena,
            reference_types[2],
            Ty::union(arena(&ret), [Ty::number(), Ty::boolean()]),
        );
    }

    #[test]
    fn flow_predicate_narrowing_expands_fully_implicit_defaults_for_values() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        interface Action<T extends string = string> { type: T }
        interface Base<P, T extends string, M = never, E = never> { payload: P; type: T }
        declare function isAction(input: unknown): input is Action;
        declare function isBase(input: unknown): input is Base<unknown, string>;
        declare const value: unknown;
        declare const baseValue: unknown;
        if (isAction(value)) {
            value;
        }
        if (isBase(baseValue)) {
            baseValue;
        }
        ",
        );

        assert_eq!(
            get_identifier_reference_types(&ret, "value")
                .into_iter()
                .map(|ty| ty.to_type_string(ret.arena))
                .collect::<Vec<_>>(),
            vec!["unknown".to_string(), "Action<string>".to_string()]
        );
        assert_eq!(
            get_identifier_reference_types(&ret, "baseValue")
                .into_iter()
                .map(|ty| ty.to_type_string(ret.arena))
                .collect::<Vec<_>>(),
            vec!["unknown".to_string(), "Base<unknown, string>".to_string()]
        );
    }

    #[test]
    fn flow_does_not_index_condition_reference_in_global_symbol_program() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const x: string | undefined;
        if (x) {
            Array;
        }
        ",
        );

        assert_eq!(
            get_identifier_reference_types(&ret, "Array")
                .into_iter()
                .map(|ty| ty.to_type_string(ret.arena))
                .collect::<Vec<_>>(),
            vec!["ArrayConstructor".to_string()]
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

        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "z"),
            Ty::union(arena, [Ty::string(), Ty::undefined()]),
        );
        assert_type_eq(
            arena,
            get_identifier_reference_types(&ret, "y"),
            vec![
                Ty::union(arena, [Ty::string(), Ty::number(), Ty::boolean()]),
                Ty::string(),
            ],
        );
    }

    #[test]
    fn conditional_template_uses_declared_literal_in_unreachable_arm() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        const arg = 'something';
        const msg = typeof arg === 'string' ? arg : `arg = ${arg}`;
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "msg").to_type_string(ret.arena),
            "\"something\" | \"arg = something\""
        );
        assert_eq!(
            get_identifier_reference_types(&ret, "arg")
                .into_iter()
                .map(|ty| ty.to_type_string(ret.arena))
                .collect::<Vec<_>>(),
            vec![
                "\"something\"".to_string(),
                "\"something\"".to_string(),
                "never".to_string(),
            ]
        );
    }

    #[test]
    fn conditional_template_does_not_fold_flow_narrowed_mutable_value() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare let value: "a" | "b";
        const msg = value === "a" ? `${value}` : "fallback";
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "msg").to_type_string(ret.arena),
            "string"
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
            get_first_symbol_type(&ret, "value").to_type_string(ret.arena),
            "TData | (TData & ({} | null))"
        );
        assert_eq!(
            get_identifier_reference_types(&ret, "previous")
                .into_iter()
                .map(|ty| ty.to_type_string(ret.arena))
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
        assert_type_eq(
            ret.arena,
            reference_types[0],
            Ty::union(arena(&ret), [Ty::string(), Ty::number()]),
        );
        assert_eq!(reference_types[1], Ty::string());
        assert_type_eq(
            ret.arena,
            reference_types[2],
            Ty::union(arena(&ret), [Ty::string(), Ty::number()]),
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

        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "before"),
            Ty::array(arena, Ty::any()),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "afterPush"),
            Ty::array(arena, Ty::number()),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "afterWrite"),
            Ty::array(arena, Ty::union(arena, [Ty::number(), Ty::string()])),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "afterReset"),
            Ty::array(arena, Ty::boolean()),
        );
    }

    #[test]
    fn type_handle_is_four_bytes() {
        assert_eq!(std::mem::size_of::<Ty>(), 4);
    }

    #[test]
    fn error_types_are_distinct_but_any_like() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "");
        let arena = arena(&ret);
        let checker = checker(&ret);
        let error = Ty::error(arena, TypeErrorKind::UnresolvedType);

        assert!(error.is_error(arena));
        assert_eq!(error.error_kind(arena), Some(TypeErrorKind::UnresolvedType));
        assert_ne!(error, Ty::any());
        assert_eq!(error.to_type_string(arena), "any");
        assert_eq!(error.enum_variant_name(arena), "TyError");
        assert!(checker.is_assignable_to(error, Ty::number()));
        assert!(checker.is_assignable_to(Ty::number(), error));
        assert!(checker.is_assignable_to(error, Ty::unknown()));
        assert!(!checker.is_assignable_to(error, Ty::never()));
        assert_eq!(Ty::union(arena, [error, Ty::string()]), error);
        assert_eq!(Ty::intersection(arena, [error, Ty::string()]), error);
    }

    #[test]
    fn unresolved_symbols_produce_error_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const value = missingSymbol;");
        let arena = arena(&ret);
        let value_type = get_global_symbol_type(&ret, "value");

        assert_eq!(
            value_type.error_kind(arena),
            Some(TypeErrorKind::UnresolvedSymbol)
        );
        assert_eq!(value_type.to_type_string(arena), "any");
    }

    #[test]
    fn intersection_with_any_reduces_to_any() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "");
        let arena = arena(&ret);
        let literal = Ty::string_literal(arena, "foo");

        assert_eq!(Ty::intersection(arena, [Ty::any(), literal]), Ty::any());
        assert_eq!(Ty::intersection(arena, [literal, Ty::any()]), Ty::any());
    }

    #[test]
    fn assignability_handles_basic_and_structural_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "");
        let checker = checker(&ret);
        let arena = arena(&ret);

        assert!(checker.is_assignable_to(Ty::number(), Ty::number()));
        assert!(checker.is_assignable_to(Ty::number(), Ty::any()));
        assert!(checker.is_assignable_to(Ty::string(), Ty::unknown()));
        assert!(!checker.is_assignable_to(Ty::number(), Ty::string()));
        assert!(checker.is_assignable_to(
            Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal),
            Ty::number()
        ));
        assert!(checker.is_assignable_to(
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

        assert!(checker.is_assignable_to(source, target));
        assert!(!checker.is_assignable_to(target, source));
    }

    #[test]
    fn assignability_handles_complex_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "");
        let checker = checker(&ret);
        let arena = arena(&ret);

        // Test that a function type is assignable to a more general function type
        assert!(checker.is_assignable_to(
            Ty::function(arena, vec![], vec![], Ty::string()),
            Ty::function(arena, vec![], vec![], Ty::any())
        ));

        // Regression test: Check that thenable is assignable to an intersection type
        let thenable = Ty::object(
            arena,
            [Ty::property(
                "then",
                Ty::function(arena, vec![], vec![], Ty::any()),
            )],
        );
        let intersection = Ty::intersection(arena, [Ty::primitive_object(), thenable]);
        assert!(checker.is_assignable_to(thenable, intersection));
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
            get_global_symbol_type(&ret, "streamedQuery").to_type_string(ret.arena),
            "<TQueryFnData, TData>({ streamFn, refetchMode, reducer, initialValue, }: StreamedQueryParams<TQueryFnData, TData>) => TData"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "streamFn")
                .to_type_string(ret.arena),
            "(context: TQueryFnData) => TQueryFnData"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "refetchMode")
                .to_type_string(ret.arena),
            "\"append\" | \"reset\" | \"replace\""
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "reducer").to_type_string(ret.arena),
            "(acc: TData, chunk: TQueryFnData) => TData"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "streamedQuery", "initialValue")
                .to_type_string(ret.arena),
            "TData"
        );
        assert_type_eq(
            ret.arena,
            get_first_symbol_type(&ret, "items"),
            Ty::type_reference(arena(&ret), "TData", std::iter::empty()),
        );
        assert_type_eq(
            ret.arena,
            get_first_symbol_type(&ret, "chunk"),
            Ty::type_reference(arena(&ret), "TQueryFnData", std::iter::empty()),
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

        assert_type_eq(
            arena,
            get_first_symbol_type(&ret, "data"),
            infinite_data_type,
        );
        assert_type_eq(arena, get_first_symbol_type(&ret, "todo"), todo_type);
        assert_eq!(
            get_object_property_types(&ret, "reducer")[0].to_type_string(ret.arena),
            "(data: InfiniteData<Todo, number>, todo: Todo) => { pages: Todo[]; pageParams: number[]; }"
        );
        assert!(contains_type(
            arena,
            &get_object_property_types(&ret, "pages"),
            Ty::array(arena, todo_type),
        ));
        assert!(contains_type(
            arena,
            &get_object_property_types(&ret, "pages"),
            Ty::array(arena, Ty::never()),
        ));
        assert!(contains_type(
            arena,
            &get_object_property_types(&ret, "pageParams"),
            Ty::array(arena, Ty::never()),
        ));
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
            get_first_symbol_type(&ret, "context").to_type_string(ret.arena),
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
            get_first_symbol_type(&ret, "context").to_type_string(ret.arena),
            "{ queryKey: TQueryKey; pageParam?: unknown; }"
        );
        assert_eq!(
            get_symbol_type_in_function(&ret, "useParams", "streamFn").to_type_string(ret.arena),
            "(context: { queryKey: TQueryKey; pageParam?: unknown; }) => void"
        );
    }

    #[test]
    #[ignore = "TODO: Fix type argument printing"]
    fn printing_type_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            interface Box<T> {
                value: T;
            }

            function box<T>(value: T): Box<T> {
                return { value };
            }

            interface Iterable<T, TReturn = any, TNext = any> {
                [Symbol.iterator](): Iterator<T, TReturn, TNext>;
            }

            function from<T>(iterable: Iterable<T>): Array<T> {
            }
            ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "box").to_type_string(ret.arena),
            "<T>(value: T) => Box<T>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "from").to_type_string(ret.arena),
            "<T>(iterable: Iterable<T>): Array<T>"
        )
    }

    #[test]
    #[ignore = "TODO: Fix type argument printing"]
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
            get_global_symbol_type(&ret, "streamedQuery").to_type_string(ret.arena),
            "<TQueryFnData = unknown, TData = TQueryFnData[], TQueryKey extends QueryKey = readonly unknown[]>({ streamFn, initialValue, }: StreamedQueryParams<TQueryFnData, TData, TQueryKey>) => QueryFunction<TData, TQueryKey>"
        );
        assert_eq!(
            get_type_alias_type(&ret, "QueryMeta").to_type_string(ret.arena),
            "{ [x: string]: unknown; }"
        );
        assert_eq!(
            get_type_alias_type(&ret, "InferDataFromTag").to_type_string(ret.arena),
            "TTaggedQueryKey extends { [dataTagSymbol]: infer TaggedValue; [dataTagErrorSymbol]: unknown; } ? TaggedValue : TQueryFnData"
        );
        assert_eq!(
            get_type_alias_type(&ret, "TaggedTodoData").to_type_string(ret.arena),
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
            get_first_symbol_type(&ret, "signalLessContext").to_type_string(ret.arena),
            "OmitKeyof<{ client: QueryClient; queryKey: TQueryKey; signal: AbortSignal; meta: QueryMeta | undefined; pageParam?: unknown; direction?: unknown; }, \"signal\">"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "meta").to_type_string(ret.arena),
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
            get_global_symbol_type(&ret, "dataTagSymbol").to_type_string(ret.arena),
            "unique symbol"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "aliasValue").to_type_string(ret.arena),
            "typeof dataTagSymbol"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "tagged").to_type_string(ret.arena),
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
            get_type_alias_type(&ret, "UnsetMarker").to_type_string(ret.arena),
            "unique symbol"
        );
    }

    #[test]
    fn global_undefined_reference_has_type_at_location() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const value = [undefined];");
        let checker = checker(&ret);
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

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "values"),
            Ty::array(arena(&ret), Ty::number()),
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

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "values"),
            Ty::array(arena(&ret), Ty::number()),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "readonlyValues"),
            Ty::readonly_array(arena(&ret), Ty::string()),
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
        let checker = CheckerBuilder::new().build(&store);
        let symbol_id = store
            .entry(program_id)
            .unwrap()
            .semantic()
            .scoping()
            .get_root_binding(Ident::from("values"))
            .unwrap();

        assert_type_eq(
            checker.arena,
            checker.get_type_of_symbol(SymbolRef::new(program_id, symbol_id)),
            Ty::type_reference(checker.arena, "Array", [Ty::number()]),
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
            get_global_symbol_type(&ret, "variadic").to_type_string(ret.arena),
            "[...string[], { huh: boolean; }]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "optional").to_type_string(ret.arena),
            "[(number | undefined)?]"
        );
    }

    #[test]
    fn tuple_spreads_are_limited_to_ten_thousand_elements() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type T0 = [any];
        type T1 = [...T0, ...T0];
        type T2 = [...T1, ...T1];
        type T3 = [...T2, ...T2];
        type T4 = [...T3, ...T3];
        type T5 = [...T4, ...T4];
        type T6 = [...T5, ...T5];
        type T7 = [...T6, ...T6];
        type T8 = [...T7, ...T7];
        type T9 = [...T8, ...T8];
        type T10 = [...T9, ...T9];
        type T11 = [...T10, ...T10];
        type T12 = [...T11, ...T11];
        type T13 = [...T12, ...T12];
        type T14 = [...T13, ...T13];

        const a0 = [0] as const;
        const a1 = [...a0, ...a0] as const;
        const a2 = [...a1, ...a1] as const;
        const a3 = [...a2, ...a2] as const;
        const a4 = [...a3, ...a3] as const;
        const a5 = [...a4, ...a4] as const;
        const a6 = [...a5, ...a5] as const;
        const a7 = [...a6, ...a6] as const;
        const a8 = [...a7, ...a7] as const;
        const a9 = [...a8, ...a8] as const;
        const a10 = [...a9, ...a9] as const;
        const a11 = [...a10, ...a10] as const;
        const a12 = [...a11, ...a11] as const;
        const a13 = [...a12, ...a12] as const;
        const a14 = [...a13, ...a13] as const;
        ",
        );

        let TypeData::Tuple(t13) = ret.arena.type_data(get_type_alias_type(&ret, "T13")) else {
            panic!("expected T13 to remain a tuple");
        };
        assert_eq!(t13.elements.len(), 8192);
        let TypeData::Tuple(a13) = ret.arena.type_data(get_global_symbol_type(&ret, "a13")) else {
            panic!("expected a13 to remain a tuple");
        };
        assert_eq!(a13.elements.len(), 8192);
        for ty in [
            get_type_alias_type(&ret, "T14"),
            get_global_symbol_type(&ret, "a14"),
        ] {
            assert_eq!(
                ty.error_kind(ret.arena),
                Some(TypeErrorKind::TupleSizeExceeded)
            );
            assert_eq!(ty.to_type_string(ret.arena), "any");
        }

        let tuple_9999 = Ty::tuple(ret.arena, vec![TupleElement::Regular(Ty::any()); 9999]);
        let TypeData::Tuple(tuple) = ret
            .arena
            .type_data(Ty::tuple(ret.arena, vec![TupleElement::Rest(tuple_9999)]))
        else {
            panic!("expected a 9,999-element spread to remain a tuple");
        };
        assert_eq!(tuple.elements.len(), 9999);
        let oversized = Ty::tuple(
            ret.arena,
            vec![
                TupleElement::Regular(Ty::any()),
                TupleElement::Rest(tuple_9999),
            ],
        );
        assert_eq!(
            oversized.error_kind(ret.arena),
            Some(TypeErrorKind::TupleSizeExceeded)
        );
        assert_eq!(oversized.to_type_string(ret.arena), "any");
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
            get_global_symbol_type(&ret, "value").to_type_string(ret.arena),
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
            get_global_symbol_type(&ret, "value").to_type_string(ret.arena),
            "string"
        );
    }

    #[test]
    fn conditional_infer_extracts_object_property_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const value: { value: number } extends { value: infer U } ? U : never;
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value").to_type_string(ret.arena),
            "number"
        );
    }

    #[test]
    fn conditional_infer_merges_repeated_candidates() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const value: { a: string; b: number } extends { a: infer U; b: infer U } ? U : never;
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value").to_type_string(ret.arena),
            "string | number"
        );
    }

    #[test]
    fn conditional_infer_merges_repeated_constrained_candidates() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const value: { a: "ready"; b: "set" } extends { a: infer U extends string; b: infer U extends string } ? U : never;
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value").to_type_string(ret.arena),
            "\"ready\" | \"set\""
        );
    }

    #[test]
    fn conditional_infer_extracts_tuple_rest() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const value: [string, number] extends [infer Head, ...infer Rest] ? Rest : never;
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "value").to_type_string(ret.arena),
            "[number]"
        );
    }

    #[test]
    fn conditional_infer_extracts_function_signature_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const returnValue: (() => string) extends (() => infer R) ? R : never;
        declare const parameterValue: ((value: string) => void) extends ((value: infer P) => void) ? P : never;
        ",
        );

        assert_eq!(
            get_global_symbol_type(&ret, "returnValue").to_type_string(ret.arena),
            "string"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "parameterValue").to_type_string(ret.arena),
            "string"
        );
    }

    #[test]
    fn indexed_access_resolves_tuple_numeric_literal_indices() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const first: ["yes", "no"][0];
        declare const second: ["yes", "no"][1];
        declare const either: ["yes", "no"][0 | 1];
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "first").to_type_string(ret.arena),
            "\"yes\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "second").to_type_string(ret.arena),
            "\"no\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "either").to_type_string(ret.arena),
            "\"yes\" | \"no\""
        );
    }

    #[test]
    fn conditional_infer_return_type_of_generic_function_falls_back_to_unknown() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type ReturnTypeOf<T extends (...args: any) => any> = T extends (...args: any) => infer R ? R : any;
        type Value = ReturnTypeOf<<T>() => T>;
        ",
        );

        assert_eq!(
            get_type_alias_type(&ret, "Value").to_type_string(ret.arena),
            "unknown"
        );
    }

    #[test]
    fn conditional_infer_return_type_from_callable_interface() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type ReturnTypeOf<T> = T extends (...args: any) => infer R ? R : any;
        interface Callable {
            (value: number): { value: number };
            readonly label: string;
        }
        type Value = ReturnTypeOf<Callable>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Value").to_type_string(ret.arena),
            "{ value: number; }"
        );
    }

    #[test]
    fn conditional_tuple_index_reduces_redux_at_least_ts35_pattern() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type ReturnTypeOf<T extends (...args: any) => any> = T extends (...args: any) => infer R ? R : any;
        type IsAny<T, True, False = never> = true | false extends (T extends never ? true : false) ? True : False;
        type IsUnknown<T, True, False = never> = unknown extends T ? IsAny<T, False, True> : False;
        type AtLeastTS35<True, False> = [True, False][IsUnknown<ReturnTypeOf<<T>() => T>, 0, 1>];
        type Value = AtLeastTS35<"yes", "no">;
        type Deferred<T> = AtLeastTS35<IsUnknown<T, "yes", "no">, "fallback">;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Value").to_type_string(ret.arena),
            "\"yes\""
        );
        assert_eq!(
            get_type_alias_type(&ret, "Deferred").to_type_string(ret.arena),
            "unknown extends T ? IsAny<T, \"no\", \"yes\"> : \"no\""
        );
    }

    #[test]
    fn conditional_infer_shadows_outer_type_parameter_substitution() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const x = 1;");
        let checker = checker(&ret);
        let arena = arena(&ret);
        let outer_array = Ty::array(arena, Ty::string());
        let conditional = Ty::conditional(
            arena,
            Ty::type_reference(arena, "T", []),
            Ty::array(arena, Ty::infer(arena, Ty::type_parameter("T", None, None))),
            Ty::type_reference(arena, "T", []),
            Ty::never(),
            false,
        );
        let mapper = TypeMapper::single(Ty::type_reference(arena, "T", []), outer_array);

        assert_eq!(checker.instantiate_type(conditional, &mapper), Ty::string());
    }

    #[test]
    fn generic_instantiations_are_cached_by_target_and_mapper() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "const x = 1;");
        let checker = checker(&ret);
        let arena = arena(&ret);
        let target = Ty::object(
            arena,
            [Ty::property("value", Ty::type_reference(arena, "T", []))],
        );
        let first_mapper = TypeMapper::single(Ty::type_reference(arena, "T", []), Ty::string());
        let second_mapper = TypeMapper::single(Ty::type_reference(arena, "T", []), Ty::string());

        assert_eq!(
            checker.instantiate_type(target, &first_mapper),
            checker.instantiate_type(target, &second_mapper)
        );
    }

    #[test]
    fn recursive_type_instantiation_depth_produces_error_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type TupleOf<T, N extends number> = N extends N ? number extends N ? T[] : BuildTuple<T, N, []> : never;
        type BuildTuple<T, N extends number, R extends unknown[]> = R['length'] extends N ? R : BuildTuple<T, N, [T, ...R]>;
        type Small = TupleOf<number, 4>;
        type Value = TupleOf<number, 1000>;
        ",
        );

        let small_type = get_type_alias_type(&ret, "Small");
        let TypeData::Tuple(small) = ret.arena.type_data(small_type) else {
            panic!(
                "expected a tuple, got {}",
                small_type.to_type_string(ret.arena)
            );
        };
        assert_eq!(small.elements.len(), 4);
        let value = get_type_alias_type(&ret, "Value");
        assert_eq!(
            value.error_kind(ret.arena),
            Some(TypeErrorKind::TypeInstantiationDepthExceeded)
        );
        assert_eq!(value.to_type_string(ret.arena), "any");
    }

    #[test]
    fn recursive_conditional_inference_defers_unresolved_active_aliases() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type ParseSuccess<R extends string> = { rest: R };
        type ParseManyWhitespace<S extends string> =
            S extends ` ${infer R0}`
                ? ParseManyWhitespace<R0> extends ParseSuccess<infer R1>
                    ? ParseSuccess<R1>
                    : null
                : ParseSuccess<S>;
        type Generic<S extends string> = ParseManyWhitespace<S>;
        ",
        );

        let ty = get_type_alias_type(&ret, "Generic");
        assert_ne!(ty, Ty::any());
        assert!(
            ty.to_type_string(ret.arena)
                .contains("ParseManyWhitespace<R0>")
        );
    }

    #[test]
    fn recursive_tuple_rest_aliases_are_preserved_while_active() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        type PromisedTuple<L extends any[], U = (...args: L) => void> =
            U extends (h: infer H, ...args: infer R) =>
                [Promise<H>, ...PromisedTuple<R>] ? [] : [];
        type Promised = PromisedTuple<[1, 2, 3]>;
        ",
        );

        let promised = get_type_alias_type(&ret, "Promised");
        let TypeData::Tuple(tuple) = ret.arena.type_data(promised) else {
            panic!(
                "expected an empty tuple, got {}",
                promised.to_type_string(ret.arena)
            );
        };
        assert!(tuple.elements.is_empty());
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
            get_type_alias_type(&ret, "OmitKeyof").to_type_string(ret.arena),
            "{ [P in Exclude<keyof TObject, TKey>]: TObject[P]; }"
        );
    }

    #[test]
    fn template_literal_type_resolves_qualified_enum_member() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
            enum ABC {
                A = "A",
                B = "B",
            }
            type Value = `${ABC.A}`;
            "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Value").to_type_string(ret.arena),
            "\"A\""
        );
    }

    #[test]
    fn type_alias_union_constituents_match_typescript_alias_display_rules() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type StringA = string;
        type StringB = string;
        type AutoKeyword = "auto";
        type One = 1;
        type Two = 2;
        type BooleanLogicExpression = ["and", ...Expression[]] | ["not", Expression];
        type Expression = BooleanLogicExpression | "true" | "false";
        type ObjAlias = { x: number };

        type PrimitiveAliases = StringA | StringB;
        type LiteralAliasWithPrimitive = AutoKeyword | string;
        type LiteralAliases = One | Two;
        type NamedUnionAlias = BooleanLogicExpression | "true" | "false";
        type ObjectAlias = ObjAlias | string;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "PrimitiveAliases").to_type_string(ret.arena),
            "string"
        );
        assert_eq!(
            get_type_alias_type(&ret, "LiteralAliasWithPrimitive").to_type_string(ret.arena),
            "string"
        );
        assert_eq!(
            get_type_alias_type(&ret, "LiteralAliases").to_type_string(ret.arena),
            "1 | 2"
        );
        assert_eq!(
            get_type_alias_type(&ret, "NamedUnionAlias").to_type_string(ret.arena),
            "BooleanLogicExpression | \"true\" | \"false\""
        );
        assert_eq!(
            get_type_alias_type(&ret, "ObjectAlias").to_type_string(ret.arena),
            "ObjAlias | string"
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
            get_type_alias_type(&ret, "Params").to_type_string(ret.arena),
            "{ refetchMode?: \"append\" | \"reset\"; }"
        );
    }

    #[test]
    fn checker_returns_index_infos_of_structured_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const direct: {
            [key: string]: number;
            readonly [index: number]: number;
        };
        declare const intersection: {
            [left: string]: number;
        } & {
            [right: number]: boolean;
        };
        declare const union: {
            [left: string]: number;
        } | {
            [right: number]: boolean;
        };
        declare const empty: {};
        "#,
        );
        let checker = checker(&ret);
        let index_info_shapes = |name: &str| {
            checker
                .get_index_infos_of_type(get_global_symbol_type(&ret, name))
                .into_iter()
                .map(|info| (info.name, info.key_type, info.value_type, info.readonly))
                .collect::<Vec<_>>()
        };

        assert_eq!(
            index_info_shapes("direct"),
            vec![
                ("key", Ty::string(), Ty::number(), false),
                ("index", Ty::number(), Ty::number(), true),
            ]
        );
        assert_eq!(
            index_info_shapes("intersection"),
            vec![
                ("left", Ty::string(), Ty::number(), false),
                ("right", Ty::number(), Ty::boolean(), false),
            ]
        );
        assert_eq!(
            index_info_shapes("union"),
            vec![
                ("left", Ty::string(), Ty::number(), false),
                ("right", Ty::number(), Ty::boolean(), false),
            ]
        );
        assert!(index_info_shapes("empty").is_empty());
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
            get_type_alias_type(&ret, "OptionalFlat").to_type_string(ret.arena),
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
    fn indexed_access_resolves_mapped_type_property_templates() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type Defaults = { requireExactProps: false };
        type Wrapper<T> = T & {};
        type Apply<SpecifiedOptions extends object> = {
            [Key in keyof Defaults]: Key extends keyof SpecifiedOptions
                ? SpecifiedOptions[Key]
                : Defaults[Key]
        };
        type ApplyWrapped<SpecifiedOptions extends object> = {
            [Key in keyof Defaults]: Key extends keyof SpecifiedOptions
                ? Wrapper<SpecifiedOptions[Key & keyof SpecifiedOptions]>
                : Defaults[Key]
        };
        type Deferred<Options extends object> = Apply<Options>["requireExactProps"];
        type DeferredWrapped<Options extends object> = ApplyWrapped<Options>["requireExactProps"];
        type Concrete = Apply<{ requireExactProps: true }>["requireExactProps"];
        type Outer<Options extends object> = Apply<Options>["requireExactProps"] extends true ? "yes" : "no";
        type OuterViaParameter<Options extends object> = _Outer<Apply<Options>>;
        type _Outer<Options extends { requireExactProps: boolean }> = Options["requireExactProps"] extends true ? "yes" : "no";
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Deferred").to_type_string(ret.arena),
            "\"requireExactProps\" extends keyof Options ? Options[\"requireExactProps\"] : false"
        );
        assert_eq!(
            get_type_alias_type(&ret, "DeferredWrapped").to_type_string(ret.arena),
            "\"requireExactProps\" extends keyof Options ? Wrapper<Options[keyof Options & \"requireExactProps\"]> : false"
        );
        assert_eq!(
            get_type_alias_type(&ret, "Concrete").to_type_string(ret.arena),
            "true"
        );
        assert_eq!(
            get_type_alias_type(&ret, "Outer").to_type_string(ret.arena),
            "(\"requireExactProps\" extends keyof Options ? Options[\"requireExactProps\"] : false) extends true ? \"yes\" : \"no\""
        );
        assert_eq!(
            get_type_alias_type(&ret, "OuterViaParameter").to_type_string(ret.arena),
            "(\"requireExactProps\" extends keyof Options ? Options[\"requireExactProps\"] : false) extends true ? \"yes\" : \"no\""
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

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "value"),
            Ty::union(arena(&ret), [Ty::boolean(), Ty::number()]),
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

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "count"),
            Ty::number_literal(arena(&ret), 1.0, "1", NumberBase::Decimal),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "label"),
            Ty::string_literal(arena(&ret), "\"ready\""),
        );
        assert_eq!(get_global_symbol_type(&ret, "enabled"), Ty::boolean_true());
    }

    #[test]
    fn get_type_at_location_checks_direct_expressions() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function make(): number;
        const numeric = 42;
        const bigint = 1n;
        const string = "hello";
        const boolean = true;
        const call = make();
        const array = [true];
        const object = { value: null };
        const functionExpression = function () {};
        const classExpression = class {};
        "#,
        );
        let checker = checker(&ret);
        let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
        let expression_types = semantic
            .nodes()
            .iter_enumerated()
            .filter_map(|(node_id, node)| {
                if !matches!(
                    semantic.nodes().parent_kind(node_id),
                    AstKind::VariableDeclarator(_)
                ) {
                    return None;
                }
                let name = match node.kind() {
                    AstKind::NumericLiteral(_) => "numeric",
                    AstKind::BigIntLiteral(_) => "bigint",
                    AstKind::StringLiteral(_) => "string",
                    AstKind::BooleanLiteral(_) => "boolean",
                    AstKind::CallExpression(_) => "call",
                    AstKind::ArrayExpression(_) => "array",
                    AstKind::ObjectExpression(_) => "object",
                    AstKind::Function(function) if function.is_expression() => "function",
                    AstKind::Class(class) if class.is_expression() => "class",
                    _ => return None,
                };
                Some((
                    name,
                    checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)),
                ))
            })
            .collect::<HashMap<_, _>>();

        assert_eq!(expression_types.len(), 9);
        assert_type_eq(
            ret.arena,
            expression_types["numeric"],
            Ty::number_literal(arena(&ret), 42.0, "42", NumberBase::Decimal),
        );
        assert_eq!(expression_types["bigint"].to_type_string(ret.arena), "1n");
        assert_eq!(
            expression_types["string"],
            Ty::string_literal(arena(&ret), "\"hello\"")
        );
        assert_eq!(expression_types["boolean"], Ty::boolean_true());
        assert_eq!(expression_types["call"], Ty::number());
        assert!(expression_types.values().all(|ty| !ty.is_none()));
    }

    #[test]
    fn type_strings_render_string_literals_with_double_quotes() {
        let allocator = Allocator::default();
        let arena = CheckerArena::new(&allocator);

        assert_eq!(
            Ty::string_literal(arena, "expects a string literal").to_type_string(arena),
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
        interface ForwardDefault<T = U, U = string> { t: T; u: U; }
        type Identity<T> = T;
        type DefaultIdentity<T = string> = T;
        type AliasBox<T> = { value: T };

        const xs = <string>x;
        const xu = <unknown>x;
        const xn = <number>x;
        const xa = <any>x;
        const identityString = x as Identity<string>;
        const identityAny = <Identity<any>>x;
        const defaultIdentity = x as DefaultIdentity;
        const aliasBox = x as AliasBox<string>;
        const boxed = (<Box>x);
        const explicitDefaultBox = (<Box<number>>x);
        const boxedValue = (<Box>x).value;
        const explicitBoxedValue = (<Box<string>>x).value;
        const selfDefaultValue = (<SelfDefault>x).value;
        const forwardDefaultT = (<ForwardDefault>x).t;
        const forwardDefaultU = (<ForwardDefault>x).u;
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "xs"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "xu"), Ty::unknown());
        assert_eq!(get_global_symbol_type(&ret, "xn"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "xa"), Ty::any());
        assert_eq!(get_global_symbol_type(&ret, "identityString"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "identityAny"), Ty::any());
        assert_eq!(
            get_global_symbol_type(&ret, "defaultIdentity"),
            Ty::string()
        );
        assert_eq!(
            get_global_symbol_type(&ret, "aliasBox").to_type_string(ret.arena),
            "AliasBox<string>"
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "boxed"),
            Ty::type_reference(arena(&ret), "Box", [Ty::number()]),
        );
        assert_eq!(
            get_global_symbol_type(&ret, "boxed").to_type_string(ret.arena),
            "Box<number>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "explicitDefaultBox").to_type_string(ret.arena),
            "Box<number>"
        );
        assert_eq!(get_global_symbol_type(&ret, "boxedValue"), Ty::number());
        assert_eq!(
            get_global_symbol_type(&ret, "explicitBoxedValue"),
            Ty::string()
        );
        assert_eq!(get_global_symbol_type(&ret, "selfDefaultValue"), Ty::any());
        assert_eq!(get_global_symbol_type(&ret, "forwardDefaultT"), Ty::any());
        assert_eq!(
            get_global_symbol_type(&ret, "forwardDefaultU"),
            Ty::string()
        );
    }

    #[test]
    fn declaration_display_handles_defaulted_type_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface BufferLike {}
        interface BufferView<TBuffer extends BufferLike = BufferLike> { buffer: TBuffer; }
        interface Stream<T = any> { value: T; }
        interface LocalIterable<T, TReturn = any, TNext = any> {}

        declare const declarations: {
            view: BufferView;
            maybeView?: BufferView;
            stream: Stream;
            iterable: LocalIterable<string>;
            explicitIterable: LocalIterable<string, any, any>;
            float: Float32Array;
            values: number[] | Float32Array;
        };
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "declarations").to_type_string(ret.arena),
            "{ view: BufferView; maybeView?: BufferView; stream: Stream; iterable: LocalIterable<string>; explicitIterable: LocalIterable<string, any, any>; float: Float32Array<ArrayBufferLike>; values: number[] | Float32Array<ArrayBufferLike>; }"
        );
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

        let arena = arena(&ret);
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "x"),
            Ty::number_literal(arena, 123.0, "123", NumberBase::Decimal),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "y"),
            Ty::string_literal(arena, "\"test\""),
        );
        assert_eq!(get_global_symbol_type(&ret, "z"), Ty::boolean_true());
    }

    #[test]
    fn generic_function_non_null_assertion_returns_non_nullable_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function foo3<T>(x: T | undefined | null) {
            return x!
        }

        const stringValue = foo3("hello");
        const undefinedValue = foo3(undefined);
        const numberValue = foo3(123 as number);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "foo3").to_type_string(ret.arena),
            "<T>(x: T | null | undefined) => NonNullable<T>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "stringValue").to_type_string(ret.arena),
            "\"hello\""
        );
        assert_eq!(get_global_symbol_type(&ret, "undefinedValue"), Ty::never());
        assert_eq!(get_global_symbol_type(&ret, "numberValue"), Ty::number());
    }

    #[test]
    fn generic_function_merges_repeated_inference_candidates() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        function choose<T>(first: T, second: T) {
            return first;
        }

        const value = choose("ready", 1);
        "#,
        );

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "value"),
            Ty::string_literal(arena(&ret), "\"ready\""),
        );
    }

    #[test]
    fn generic_function_prefers_naked_type_variable_inference_candidate() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const values: any[];
        function choose<T>(items: T[], value: T) {
            return value;
        }

        const result = choose(values, "ready");
        "#,
        );

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "result"),
            Ty::string_literal(arena(&ret), "\"ready\""),
        );
    }

    #[test]
    fn generic_function_infers_from_array_and_tuple_shapes() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function first<T>(values: T[]): T;
        declare function pair<T, U>(value: [T, U]): [T, U];
        declare function tail<T extends unknown[]>(value: [string, ...T]): T;

        const firstValue = first([1, 2]);
        const pairValue = pair([1, "ready"] as [number, string]);
        const tailValue = tail(["start", 1, true] as [string, number, boolean]);
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "firstValue"), Ty::number());
        assert_eq!(
            get_global_symbol_type(&ret, "pairValue").to_type_string(ret.arena),
            "[number, string]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "tailValue").to_type_string(ret.arena),
            "[number, boolean]"
        );
    }

    #[test]
    fn generic_function_infers_from_keyof_and_indexed_access_shapes() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const key: keyof Box<number>;
        declare const indexed: Box<number>[Key];
        declare function targetOf<T>(key: keyof T): T;
        declare function objectOf<T, K>(value: T[K]): T;

        const target = targetOf(key);
        const object = objectOf(indexed);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "target").to_type_string(ret.arena),
            "Box<number>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "object").to_type_string(ret.arena),
            "Box<number>"
        );
    }

    #[test]
    fn generic_function_resolves_indexed_access_return_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function get<T, K extends keyof T>(obj: T, key: K): T[K];

        const value = get({ value: 1, name: "ready" }, "value");
        const name = get({ value: 1, name: "ready" }, "name");
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "value"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "name"), Ty::string());
    }

    #[test]
    fn generic_function_infers_from_union_parameter_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function maybe<T>(value: T | undefined): T;
        declare function nullable<T>(value: T | null): T;
        declare function falsy<T>(value: T | false): T;
        declare function unwrapPromise<T>(value: Promise<T> | T): T;
        declare const promiseString: Promise<string>;

        const maybeValue = maybe("ready");
        const nullableValue = nullable("ready");
        const falsyValue = falsy("ready");
        const promiseValue = unwrapPromise(promiseString);
        const directValue = unwrapPromise("ready");
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "maybeValue").to_type_string(ret.arena),
            "\"ready\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "nullableValue").to_type_string(ret.arena),
            "\"ready\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "falsyValue").to_type_string(ret.arena),
            "\"ready\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "promiseValue").to_type_string(ret.arena),
            "string"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "directValue").to_type_string(ret.arena),
            "\"ready\""
        );
    }

    #[test]
    fn generic_function_infers_from_intersection_parameter_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const source: string[] & { extra: number };
        declare function extra<T>(value: string[] & T): T;

        const extraValue = extra(source);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "extraValue").to_type_string(ret.arena),
            "{ extra: number; }"
        );
    }

    #[test]
    fn generic_function_detects_same_shape_mapped_type_inference() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface Box<T> { value: T; }
        declare const mappedBox: { [P in keyof Box<number>]: Box<number>[P] };
        declare function unwrap<T>(value: { [P in keyof T]: T[P] }): T;

        const unwrapped = unwrap(mappedBox);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "unwrapped").to_type_string(ret.arena),
            "Box<number>"
        );
    }

    #[test]
    fn generic_function_infers_reverse_same_shape_mapped_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function unwrap<T>(value: { [P in keyof T]: T[P] }): T;
        declare function unwrapPartial<T>(value: { [P in keyof T]?: T[P] }): T;

        const unwrapped = unwrap({ value: 1, name: "ready" });
        const partial = unwrapPartial({ value: 1 });
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "unwrapped").to_type_string(ret.arena),
            "{ value: number; name: string; }"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "partial").to_type_string(ret.arena),
            "{ value: number; }"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "unwrap").to_type_string(ret.arena),
            "<T>(value: { [P in keyof T]: T[P]; }) => T"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "unwrapPartial").to_type_string(ret.arena),
            "<T>(value: { [P in keyof T]?: T[P] | undefined; }) => T"
        );
    }

    #[test]
    fn generic_function_infers_reverse_mapped_arrays_and_tuples() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function unwrap<T>(value: { [P in keyof T]: T[P] }): T;
        declare function unwrapReadonly<T>(value: { readonly [P in keyof T]: T[P] }): T;

        const arrayValue = unwrap([1, 2]);
        const tupleValue = unwrap([1, "ready"] as [number, string]);
        const readonlyTupleValue = unwrapReadonly([1, "ready"] as readonly [number, string]);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "arrayValue").to_type_string(ret.arena),
            "number[]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "tupleValue").to_type_string(ret.arena),
            "[number, string]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "readonlyTupleValue").to_type_string(ret.arena),
            "readonly [number, string]"
        );
    }

    #[test]
    fn generic_function_infers_through_mapped_type_parameter_constraints() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function pickish<T, K extends keyof T>(value: { [P in K]: T[P] }): T;

        const picked = pickish({ value: 1 });
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "picked").to_type_string(ret.arena),
            "{ value: number; }"
        );
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
    fn function_overloads_rank_more_specific_applicable_signature() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function literalOverload(x: string): "wide";
        declare function literalOverload(x: "ready"): "literal";

        declare function genericOverload<T>(x: T): T[];
        declare function genericOverload(x: string): string;

        declare function tiedOverload(x: string, y?: number): "first";
        declare function tiedOverload(x: string): "second";

        declare function tupleRestOverload(...args: [value: string]): "one";
        declare function tupleRestOverload(...args: [value: string, count: number]): "two";

        declare function optionalTupleRestOverload(...args: [value: string, count?: number]): "optional";
        declare function optionalTupleRestOverload(...args: [value: string, count: number, flag: boolean]): "three";

        const literalResult = literalOverload("ready");
        const genericResult = genericOverload("ready");
        const tiedResult = tiedOverload("ready");
        const tupleRestOne = tupleRestOverload("ready");
        const tupleRestTwo = tupleRestOverload("ready", 1);
        const optionalTupleRestOne = optionalTupleRestOverload("ready");
        const optionalTupleRestTwo = optionalTupleRestOverload("ready", 1);
        const optionalTupleRestThree = optionalTupleRestOverload("ready", 1, true);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "literalResult").to_type_string(ret.arena),
            "\"literal\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "genericResult").to_type_string(ret.arena),
            "string[]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "tiedResult").to_type_string(ret.arena),
            "\"first\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "tupleRestOne").to_type_string(ret.arena),
            "\"one\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "tupleRestTwo").to_type_string(ret.arena),
            "\"two\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "optionalTupleRestOne").to_type_string(ret.arena),
            "\"optional\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "optionalTupleRestTwo").to_type_string(ret.arena),
            "\"optional\""
        );
        assert_eq!(
            get_global_symbol_type(&ret, "optionalTupleRestThree").to_type_string(ret.arena),
            "\"three\""
        );
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
    fn generic_overloads_use_candidate_inference_for_applicability() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function pick<T>(x: T[]): T;
        declare function pick<T>(x: T): T;

        const value = pick("ready");
        "#,
        );

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "value"),
            Ty::string_literal(arena(&ret), "\"ready\""),
        );
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
    fn instantiated_interface_method_type_parameters_render_as_arguments() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface Interface<T> {
            unused<U extends string>(value: U): U;
            dependent<U extends T>(value: T, other: U): U;
            independent<U extends string>(value: T, other: U): U;
            unusedDefault<U = string>(value: U): U;
            independentDefault<U = string>(value: T, other: U): U;
        }

        declare const instance: Interface<number>;
        instance.unused;
        instance.dependent;
        instance.independent;
        instance.unusedDefault;
        instance.independentDefault;
        "#,
        );

        let method_types = get_static_member_expression_types(&ret, "unused")
            .into_iter()
            .chain(get_static_member_expression_types(&ret, "dependent"))
            .chain(get_static_member_expression_types(&ret, "independent"))
            .chain(get_static_member_expression_types(&ret, "unusedDefault"))
            .chain(get_static_member_expression_types(
                &ret,
                "independentDefault",
            ))
            .map(|ty| ty.to_type_string(ret.arena))
            .collect::<Vec<_>>();
        assert_eq!(
            method_types,
            vec![
                "<U extends string>(value: U) => U",
                "<U>(value: number, other: U) => U",
                "<U>(value: number, other: U) => U",
                "<U = string>(value: U) => U",
                "<U>(value: number, other: U) => U",
            ]
        );
    }

    #[test]
    fn interface_accessor_signature_locations_use_property_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface TextLike {
            get textContent(): string;
            set textContent(value: string | null);
        }
        interface ReversedTextLike {
            set textContent(value: string | null);
            get textContent(): string;
        }
        declare const value: TextLike;
        declare const reversedValue: ReversedTextLike;
        declare const literalValue: {
            get textContent(): string;
            set textContent(value: string | null);
        };
        const text = value.textContent;
        const reversedText = reversedValue.textContent;
        const literalText = literalValue.textContent;
        "#,
        );

        assert_eq!(
            get_ts_method_signature_types(&ret, "textContent"),
            vec![
                "string".to_string(),
                "string | null".to_string(),
                "string | null".to_string(),
                "string".to_string(),
                "string".to_string(),
                "string | null".to_string(),
            ]
        );
        assert_eq!(get_global_symbol_type(&ret, "text"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "reversedText"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "literalText"), Ty::string());
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
            get_global_symbol_type(&ret, "Err").to_type_string(ret.arena),
            "typeof ErrImpl & (<T>() => T)"
        );
        assert_type_eq(
            arena,
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
            ),
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
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "literalUnionResult"),
            Ty::union(
                arena,
                [
                    Ty::number_literal(arena, 2.0, "2", NumberBase::Decimal),
                    Ty::number_literal(arena, 1.0, "1", NumberBase::Decimal),
                ],
            ),
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
            get_global_symbol_type(&ret, "predicate").to_type_string(ret.arena),
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
            get_global_symbol_type(&ret, "returnsString").to_type_string(ret.arena),
            "() => Promise<string>"
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "stringResult"),
            Ty::type_reference(arena, "Promise", [Ty::string()]),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "emptyResult"),
            Ty::type_reference(arena, "Promise", [Ty::void()]),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "numberResult"),
            Ty::type_reference(arena, "Promise", [Ty::number()]),
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
            get_first_symbol_type(&ret, "stream").to_type_string(ret.arena),
            "AsyncIterable<TQueryFnData>"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "chunk").to_type_string(ret.arena),
            "Awaited<TQueryFnData>"
        );
    }

    #[test]
    fn for_await_extracts_builtin_async_generator_yield_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        async function* values() {
            yield 1;
            yield 2;
        }

        async function consume() {
            for await (const value of values()) {
                value;
            }
        }
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "value").to_type_string(ret.arena),
            "1 | 2"
        );
    }

    #[test]
    fn for_await_does_not_classify_shadowed_async_generator_as_global() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        export {};
        interface AsyncGenerator<T> {
            value: T;
        }
        declare const values: AsyncGenerator<string>;

        async function consume() {
            for await (const value of values) {
                value;
            }
        }
        "#,
        );

        assert_eq!(get_first_symbol_type(&ret, "value"), Ty::any());
    }

    #[test]
    fn structural_sync_iterable_supplies_for_of_and_for_await_element_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface NumberIterator extends Iterator<1 | 2, void> {}
        interface Numbers {
            [Symbol.iterator](): NumberIterator;
        }
        declare const numbers: Numbers;

        for (const syncValue of numbers) {
            syncValue;
        }
        async function consume() {
            for await (const asyncValue of numbers) {
                asyncValue;
            }
        }
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "syncValue").to_type_string(ret.arena),
            "1 | 2"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "asyncValue").to_type_string(ret.arena),
            "1 | 2"
        );
    }

    #[test]
    fn cyclic_iterable_heritage_does_not_produce_an_element_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface First<T> extends Second<T> {}
        interface Second<T> extends First<T> {}
        declare const values: First<string>;

        for (const value of values) {
            value;
        }
        "#,
        );

        assert_eq!(get_first_symbol_type(&ret, "value"), Ty::any());
    }

    #[test]
    fn iterable_protocol_does_not_use_a_shadowed_symbol_value() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        export {};
        declare const Symbol: { readonly iterator: unique symbol };
        interface Values {
            [Symbol.iterator](): Iterator<string>;
        }
        declare const values: Values;

        for (const value of values) {
            value;
        }
        "#,
        );

        assert_eq!(get_first_symbol_type(&ret, "value"), Ty::any());
    }

    #[test]
    fn structural_async_iterable_supplies_for_await_element_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface TextAsyncIterator {
            next(): Promise<IteratorResult<"chunk", void>>;
        }
        interface TextStream {
            [Symbol.asyncIterator](): TextAsyncIterator;
        }
        declare const stream: TextStream;

        async function consume() {
            for await (const chunk of stream) {
                chunk;
            }
        }
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "chunk").to_type_string(ret.arena),
            "\"chunk\""
        );
    }

    #[test]
    fn inherited_async_iterable_supplies_for_await_element_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface TextStream extends AsyncIterable<"chunk"> {}
        declare const stream: TextStream;

        async function consume() {
            for await (const chunk of stream) {
                chunk;
            }
        }
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "chunk").to_type_string(ret.arena),
            "\"chunk\""
        );
    }

    #[test]
    fn async_only_iterable_does_not_supply_regular_for_of_element_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        interface TextAsyncIterator {
            next(): Promise<IteratorResult<string, void>>;
        }
        interface TextStream {
            [Symbol.asyncIterator](): TextAsyncIterator;
        }
        declare const stream: TextStream;

        for (const chunk of stream) {
            chunk;
        }
        "#,
        );

        assert_eq!(get_first_symbol_type(&ret, "chunk"), Ty::any());
    }

    #[test]
    fn structural_type_literal_iterable_discriminates_yield_results() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const values: {
            [Symbol.iterator](): {
                next():
                    | { done?: false; value: "item" }
                    | { done: true; value: void };
            };
        };

        for (const value of values) {
            value;
        }
        for (const character of "text") {
            character;
        }
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "value").to_type_string(ret.arena),
            "\"item\""
        );
        assert_eq!(get_first_symbol_type(&ret, "character"), Ty::string());
    }

    #[test]
    fn spreads_materialize_interface_members_and_iterable_elements() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const promise: Promise<number>;
        const spreadPromise = { ...promise };
        declare const map: Map<string, number>;
        const spreadMap = { ...map };
        const mapObject = Object.fromEntries(map);
        declare function getObject(): Record<string, string>;
        const getObjectSpread = { ...getObject() };
        const characters = [..."text"];
        "#,
        );

        let spread_promise = get_first_symbol_type(&ret, "spreadPromise").to_type_string(ret.arena);
        assert!(spread_promise.contains("then<TResult1, TResult2>"));
        assert!(spread_promise.contains("[Symbol.toStringTag]: string"));
        let spread_map = get_first_symbol_type(&ret, "spreadMap").to_type_string(ret.arena);
        assert!(spread_map.contains("set(key: string, value: number): Map<string, number>"));
        assert!(spread_map.contains("[Symbol.iterator](): MapIterator<[string, number]>"));
        assert_eq!(
            get_first_symbol_type(&ret, "mapObject").to_type_string(ret.arena),
            "{ [k: string]: number; }"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "getObjectSpread").to_type_string(ret.arena),
            "{ [x: string]: string; }"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "characters").to_type_string(ret.arena),
            "string[]"
        );

        let shadowed_ret = parse_and_check_source(
            &allocator,
            r#"
        export {};
        interface Promise<T> { own: T }
        declare const promise: Promise<number>;
        const spreadPromise = { ...promise };
        "#,
        );
        assert_eq!(
            get_first_symbol_type(&shadowed_ret, "spreadPromise")
                .to_type_string(shadowed_ret.arena),
            "{ own: number; }"
        );

        let augmented_ret = parse_and_check_source(
            &allocator,
            r#"
        interface Map<K, V> { own: K }
        declare const map: Map<string, number>;
        const spreadMap = { ...map };
        "#,
        );
        let spread_map =
            get_first_symbol_type(&augmented_ret, "spreadMap").to_type_string(augmented_ret.arena);
        assert!(spread_map.contains("own: string"));
        assert!(spread_map.contains("clear(): void"));
    }

    #[test]
    fn spreads_materialize_class_instance_fields() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare class Box {
            value: number;
            method(): string;
        }
        declare const instance: Box;
        const instanceSpread = { ...instance };

        declare class GenericBox<T> {
            value: T;
        }
        declare const genericInstance: GenericBox<string>;
        const genericInstanceSpread = { ...genericInstance };
        "#,
        );

        assert_eq!(
            get_first_symbol_type(&ret, "instanceSpread").to_type_string(ret.arena),
            "{ value: number; }"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "genericInstanceSpread").to_type_string(ret.arena),
            "{ value: string; }"
        );
    }

    #[test]
    fn invalid_object_spreads_produce_error_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare const promise: Promise<number>;
        async function main() {
            const spreadPromise = { ...(await promise) };
        }
        const numberSpread = { ...42 };
        "#,
        );

        for name in ["spreadPromise", "numberSpread"] {
            let ty = get_first_symbol_type(&ret, name);
            assert_eq!(
                ty.error_kind(ret.arena),
                Some(TypeErrorKind::UnsupportedType)
            );
            assert_eq!(ty.to_type_string(ret.arena), "any");
        }
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

        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "promise"),
            Ty::type_reference(arena, "Promise", [Ty::unknown()]),
        );
        assert_eq!(
            get_first_symbol_type(&ret, "resolve").to_type_string(ret.arena),
            "(value: unknown) => void"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "reject").to_type_string(ret.arena),
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

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "rejected"),
            Ty::type_reference(arena(&ret), "Promise", [Ty::never()]),
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
            get_global_symbol_type(&ret, "thenMethod").to_type_string(ret.arena),
            "<TResult1, TResult2>(onfulfilled?: ((value: string) => TResult1 | PromiseLike<TResult1>) | null | undefined, onrejected?: ((reason: any) => TResult2 | PromiseLike<TResult2>) | null | undefined) => Promise<TResult1 | TResult2>"
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "thenResult"),
            Ty::type_reference(arena, "Promise", [Ty::void()]),
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "defaultThenResult"),
            Ty::type_reference(arena, "Promise", [Ty::string()]),
        );
        assert_eq!(
            get_global_symbol_type(&ret, "catchMethod").to_type_string(ret.arena),
            "<TResult>(onrejected?: ((reason: any) => TResult | PromiseLike<TResult>) | null | undefined) => Promise<TResult>"
        );
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "catchResult"),
            Ty::type_reference(arena, "Promise", [Ty::void()]),
        );
    }

    #[test]
    fn generic_function_infers_from_callback_return_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function useCallback<T>(callback: () => T): T;
        declare function configure<T>(options: { create: () => T }): T;

        const callbackValue = useCallback(() => 1);
        const objectCallbackValue = configure({ create: () => ({ value: 1 }) });
        "#,
        );

        assert_eq!(get_global_symbol_type(&ret, "callbackValue"), Ty::number());
        assert_eq!(
            get_global_symbol_type(&ret, "objectCallbackValue").to_type_string(ret.arena),
            "{ value: number; }"
        );
    }

    #[test]
    fn object_literal_callbacks_share_intra_expression_inference() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function configure<T>(options: {
            create: () => T;
            consume: (value: T) => void;
        }): T;

        const result = configure({
            create: () => ({ value: 1 }),
            consume: (item) => {
                const derivedValue = item.value;
            },
        });
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "result").to_type_string(ret.arena),
            "{ value: number; }"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "item").to_type_string(ret.arena),
            "{ value: number; }"
        );
        assert_eq!(get_first_symbol_type(&ret, "derivedValue"), Ty::number());
    }

    #[test]
    fn tuple_callbacks_share_intra_expression_inference() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        declare function configure<T>(callbacks: [() => T, (value: T) => void]): T;

        const result = configure([
            () => ({ value: 1 }),
            (item) => {
                const derivedValue = item.value;
            },
        ]);
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "result").to_type_string(ret.arena),
            "{ value: number; }"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "item").to_type_string(ret.arena),
            "{ value: number; }"
        );
        assert_eq!(get_first_symbol_type(&ret, "derivedValue"), Ty::number());
    }

    #[test]
    fn user_defined_awaited_alias_is_evaluated_normally() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type Awaited<T> = { value: T };
        type Value = Awaited<Promise<number>>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Value").to_type_string(ret.arena),
            "{ value: Promise<number>; }"
        );
    }

    #[test]
    fn awaited_primitive_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        const arrayOfPromises = [
            Promise.resolve(1),
            Promise.resolve(2),
            Promise.resolve(3),
        ];
        declare const voidPromises: Promise<void>[];
        const all = Promise.all(voidPromises);
        declare const tupleOfPromises: readonly [Promise<number>, Promise<string>];
        const allTuple = Promise.all(tupleOfPromises);
        declare const readonlyTuple: readonly [number, string];
        declare function readonlyCopy<T extends readonly unknown[]>(value: T): { readonly [P in keyof T]: T[P] };
        declare function mutableCopy<T extends readonly unknown[]>(value: T): { -readonly [P in keyof T]: T[P] };
        declare function optionalCopy<T extends readonly unknown[]>(value: T): { [P in keyof T]?: T[P] };
        declare function requiredCopy<T extends readonly unknown[]>(value: T): { [P in keyof T]-?: T[P] };
        interface AllConstructor {
            new<T extends readonly unknown[]>(values: T): Promise<{ -readonly [P in keyof T]: Awaited<T[P]> }>;
        }
        declare const All: AllConstructor;
        const readonlyCopyOfTuple = readonlyCopy([1, "ready"] as [number, string]);
        const mutableCopyOfTuple = mutableCopy(readonlyTuple);
        const optionalCopyOfTuple = optionalCopy([1, "ready"] as [number, string]);
        const requiredCopyOfTuple = requiredCopy([1, "ready"] as [number?, string?]);
        declare const optionalUndefinedTuple: [undefined?];
        declare const optionalUnionUndefinedTuple: [(number | undefined)?];
        const requiredCopyOfOptionalUndefined = requiredCopy(optionalUndefinedTuple);
        const requiredCopyOfOptionalUnionUndefined = requiredCopy(optionalUnionUndefinedTuple);
        const constructedAll = new All(tupleOfPromises);
        type T1 = Awaited<number>;
        type T2 = Awaited<Promise<void>>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "T1").to_type_string(ret.arena),
            "number"
        );
        assert_eq!(
            get_type_alias_type(&ret, "T2").to_type_string(ret.arena),
            "void"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "arrayOfPromises").to_type_string(ret.arena),
            "Promise<number>[]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "all").to_type_string(ret.arena),
            "Promise<void[]>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "allTuple").to_type_string(ret.arena),
            "Promise<[number, string]>"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "readonlyCopyOfTuple").to_type_string(ret.arena),
            "readonly [number, string]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "mutableCopyOfTuple").to_type_string(ret.arena),
            "[number, string]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "optionalCopyOfTuple").to_type_string(ret.arena),
            "[(number | undefined)?, (string | undefined)?]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "requiredCopyOfTuple").to_type_string(ret.arena),
            "[number, string]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "requiredCopyOfOptionalUndefined")
                .to_type_string(ret.arena),
            "[never]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "requiredCopyOfOptionalUnionUndefined")
                .to_type_string(ret.arena),
            "[number]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "constructedAll").to_type_string(ret.arena),
            "Promise<[number, string]>"
        );
    }

    #[test]
    fn awaited_conditional_alias_shape_resolves_nullish_branch() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type TestAwaited<T> = T extends null | undefined ? T :
            T extends object & { then(onfulfilled: infer F, ...args: infer _): any; } ?
                F extends ((value: infer V, ...args: infer _) => any) ?
                    TestAwaited<V> :
                never :
            T;

        type Nullish = TestAwaited<null | undefined>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Nullish").to_type_string(ret.arena),
            "null | undefined"
        );
    }

    #[test]
    fn awaited_conditional_alias_extracts_thenable_callback_value() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type ThenValue<T> = T extends { then(onfulfilled: infer F, ...args: infer _): any; } ?
            F extends ((value: infer V, ...args: infer _) => any) ? V : never :
            T;

        type StructuralThenable = ThenValue<{ then(onfulfilled: (value: string) => void): void }>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "StructuralThenable").to_type_string(ret.arena),
            "string"
        );
    }

    #[test]
    fn awaited_conditional_alias_recursively_unwraps_simple_thenable_value() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type TestAwaited<T> = T extends null | undefined ? T :
            T extends { then(onfulfilled: infer F, ...args: infer _): any; } ?
                F extends ((value: infer V, ...args: infer _) => any) ?
                    TestAwaited<V> :
                never :
            T;

        type StructuralThenable = TestAwaited<{ then(onfulfilled: (value: string) => void): void }>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "StructuralThenable").to_type_string(ret.arena),
            "string"
        );
    }

    #[test]
    fn awaited_conditional_alias_shape_resolves_non_thenable_false_branch() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type TestAwaited<T> = T extends null | undefined ? T :
            T extends object & { then(onfulfilled: infer F, ...args: infer _): any; } ?
                F extends ((value: infer V, ...args: infer _) => any) ?
                    TestAwaited<V> :
                never :
            T;

        type Primitive = TestAwaited<number>;
        type PlainObject = TestAwaited<{ value: string }>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "Primitive").to_type_string(ret.arena),
            "number"
        );
        assert_eq!(
            get_type_alias_type(&ret, "PlainObject").to_type_string(ret.arena),
            "{ value: string; }"
        );
    }

    #[test]
    fn awaited_conditional_alias_shape_matches_lib_thenables() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type TestAwaited<T> = T extends null | undefined ? T :
            T extends object & { then(onfulfilled: infer F, ...args: infer _): any; } ?
                F extends ((value: infer V, ...args: infer _) => any) ?
                    TestAwaited<V> :
                never :
            T;

        type StructuralThenable = TestAwaited<{ then(onfulfilled: (value: string) => void): void }>;
        type NestedStructuralThenable = TestAwaited<{
            then(onfulfilled: (value: { then(onfulfilled: (value: number) => void): void }) => void): void;
        }>;
        type PromiseValue = TestAwaited<Promise<string>>;
        type NestedPromiseValue = TestAwaited<Promise<Promise<number>>>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "StructuralThenable").to_type_string(ret.arena),
            "string"
        );
        assert_eq!(
            get_type_alias_type(&ret, "NestedStructuralThenable").to_type_string(ret.arena),
            "number"
        );
        assert_eq!(
            get_type_alias_type(&ret, "PromiseValue").to_type_string(ret.arena),
            "string"
        );
        assert_eq!(
            get_type_alias_type(&ret, "NestedPromiseValue").to_type_string(ret.arena),
            "number"
        );
    }

    #[test]
    fn awaited_conditional_alias_shape_rejects_non_callable_then_argument() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            r#"
        type TestAwaited<T> = T extends null | undefined ? T :
            T extends { then(onfulfilled: infer F, ...args: infer _): any; } ?
                F extends ((value: infer V, ...args: infer _) => any) ?
                    TestAwaited<V> :
                never :
            T;

        type NonCallableThenArgument = TestAwaited<{ then(onfulfilled: number): void }>;
        "#,
        );

        assert_eq!(
            get_type_alias_type(&ret, "NonCallableThenArgument").to_type_string(ret.arena),
            "never"
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
        let arena = CheckerArena::new(store.allocator());
        let ret = ParseAndCheck {
            store,
            program_id,
            arena,
        };

        assert_eq!(
            get_global_symbol_type(&ret, "returnsPromise").to_type_string(ret.arena),
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

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "x"),
            Ty::object(arena(&ret), [Ty::property("value", Ty::number())]),
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

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "explicit"),
            Ty::type_reference(arena(&ret), "Box", [Ty::string()]),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "inferred"),
            Ty::type_reference(arena(&ret), "Box", [Ty::number()]),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "fromExplicitCall"),
            Ty::type_reference(arena(&ret), "Box", [Ty::string()]),
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
        declare function dependent<T, U = T>(x: T): U;
        declare function unresolved<T>(): T;

        const fromDefault = foo();
        const fromInference = foo(a);
        const fromDependentDefault = dependent("ready");
        const unresolvedValue = unresolved();
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "fn").to_type_string(ret.arena),
            "<T = A>(x: T) => T"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(ret.arena),
            "<T = A>(x?: T) => T"
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "fromDefault"),
            Ty::type_reference(arena(&ret), "A", std::iter::empty()),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "fromInference"),
            Ty::type_reference(arena(&ret), "A", std::iter::empty()),
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromDependentDefault"),
            Ty::string()
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "unresolvedValue"),
            Ty::type_reference(arena(&ret), "T", std::iter::empty()),
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
        declare function fallbackToConstraint<T extends string>(): T;

        const fromConstraint = foo();
        const fromInference = foo(a);
        const stringConstraint = fallbackToConstraint();
        "#,
        );

        assert_eq!(
            get_global_symbol_type(&ret, "fn").to_type_string(ret.arena),
            "<T extends A>(x: T) => T"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "foo").to_type_string(ret.arena),
            "<T extends A, U extends T = T>(x?: T, y?: U) => [T, U]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromConstraint").to_type_string(ret.arena),
            "[A, A]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "fromInference").to_type_string(ret.arena),
            "[A, A]"
        );
        assert_eq!(
            get_global_symbol_type(&ret, "stringConstraint"),
            Ty::string()
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
            get_global_symbol_type(&ret, "source").to_type_string(ret.arena),
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

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "c"),
            Ty::type_reference(arena(&ret), "Foo", std::iter::empty()),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "x"),
            Ty::object(arena(&ret), [Ty::property("b", Ty::number())]),
        );
    }

    #[test]
    fn new_expression_fills_unresolved_construct_inference_with_unknown() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
        declare const Factory: { new <T>(): T };

        const value = new Factory();
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "value"), Ty::unknown());
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

        assert_type_eq(
            ret.arena,
            get_first_symbol_type(&ret, "val"),
            Ty::type_reference(arena(&ret), "Ship", std::iter::empty()),
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

        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "mapped"),
            Ty::array(arena, Ty::type_reference(arena, "Promise", [Ty::number()])),
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
        assert_type_eq(
            arena,
            get_global_symbol_type(&ret, "lengths"),
            Ty::array(arena, Ty::number()),
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
        const fnText = (() => {}).toLocaleString();
        const functionLength = ((value: number) => value).length;
        const fixed = (1).toFixed();
        const boolValue = (true).valueOf();
        const symbolText = key.toString();
        const bigValue = big.valueOf();
        const regexText = /abc/.toString();
        const regexTest = /abc/.test('abc');
        const regexHasOwn = /abc/.hasOwnProperty('source');
        const regexLowercase = /abc/.tostring();
        ",
        );

        assert_eq!(get_global_symbol_type(&ret, "objectText"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "fnText"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "functionLength"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "fixed"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "boolValue"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "symbolText"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "bigValue"), Ty::bigint());
        assert_eq!(get_global_symbol_type(&ret, "regexText"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "regexTest"), Ty::boolean());
        assert_eq!(get_global_symbol_type(&ret, "regexHasOwn"), Ty::boolean());
        let regex_lowercase = get_global_symbol_type(&ret, "regexLowercase");
        assert_eq!(
            regex_lowercase.error_kind(ret.arena),
            Some(TypeErrorKind::UnresolvedMember)
        );
        assert_eq!(regex_lowercase.to_type_string(ret.arena), "any");
    }

    #[test]
    fn member_expression_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            type User = {
                id: number;
                name: string;
            };
            const user: User = { id: 1, name: 'Alice' };
            const userId = user.id;
            const userName = user.name;

            const hash: Record<string, string> = { a: '1', b: '2' };
            const hashValue = hash.a;

            declare const rec: Record<'type', unknown>;
            const recValue = rec.type;
            const recValue2 = rec.x;
            ",
        );

        assert_eq!(get_global_symbol_type(&ret, "userId"), Ty::number());
        assert_eq!(get_global_symbol_type(&ret, "userName"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "hashValue"), Ty::string());
        assert_eq!(get_global_symbol_type(&ret, "recValue"), Ty::unknown());
        let rec_value2 = get_global_symbol_type(&ret, "recValue2");
        assert_eq!(
            rec_value2.error_kind(ret.arena),
            Some(TypeErrorKind::UnresolvedMember)
        );
        assert_eq!(rec_value2.to_type_string(ret.arena), "any");
    }

    #[test]
    fn chain_expression_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "
            type User = {
                id: number;
                name: string;
            };

            type Profile = {
                name: string
                age?: number
                greet?: (message: string) => string
                tags?: string[]
                nested?: {
                    count: number
                    getCount?: () => number
                    values?: Array<{ label: string }>
                }
            }
            declare const user: User | undefined = { id: 1, name: 'Alice' };
            const userId = user?.id;
            const userName = user?.name;

            const userId2 = user?.['id'];
            const userName2 = user?.['name'];

            declare const index: number
            declare const maybeUser: Profile | undefined
            const optionalNestedArray = maybeUser?.nested?.values?.[index]
            ",
        );

        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "userId"),
            Ty::union(arena(&ret), [Ty::number(), Ty::undefined()]),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "userName"),
            Ty::union(arena(&ret), [Ty::string(), Ty::undefined()]),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "userId2"),
            Ty::union(arena(&ret), [Ty::number(), Ty::undefined()]),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "userName2"),
            Ty::union(arena(&ret), [Ty::string(), Ty::undefined()]),
        );
        assert_type_eq(
            ret.arena,
            get_global_symbol_type(&ret, "optionalNestedArray"),
            Ty::object(arena(&ret), [Ty::property("label", Ty::string())])
                .or_undefined(arena(&ret)),
        );
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
            get_global_symbol_type(&ret, "foo").to_type_string(ret.arena),
            "(a?: number) => number"
        );
        assert_type_eq(
            ret.arena,
            get_symbol_type_in_function(&ret, "foo", "a"),
            Ty::union(arena(&ret), [Ty::number(), Ty::undefined()]),
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
            get_global_symbol_type(&ret, "foo").to_type_string(ret.arena),
            "(a: string, b?: string, c?: number, ...d: number[]) => void"
        );
        let ty = get_global_symbol_type(&ret, "foo");
        let TypeData::Function(function) = ret.arena.type_data(ty) else {
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

        assert_type_eq(
            arena,
            get_first_symbol_type(&ret, "ab"),
            Ty::function(
                arena,
                [],
                [Ty::rest_parameter(
                    arena.str("args"),
                    Ty::type_reference(arena, arena.str("A"), []),
                )],
                Ty::type_reference(arena, arena.str("B"), []),
            ),
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
            get_first_symbol_type(&ret, "predicate").to_type_string(ret.arena),
            "(value: T) => value is S"
        );
        assert_eq!(
            get_first_symbol_type(&ret, "assertion").to_type_string(ret.arena),
            "(value: unknown) => asserts value is string"
        );
    }

    #[test]
    fn test_get_global_type() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(&allocator, "");
        let checker = checker(&ret);

        // Now test things that should be in the global environment:
        assert_type_eq(
            ret.arena,
            get_global_type(&ret, ret.program_id, "Promise"),
            Some(Ty::type_reference(
                arena(&ret),
                "Promise",
                std::iter::empty(),
            )),
        );
        assert_type_eq(
            ret.arena,
            checker.get_global_promise_type(ret.program_id),
            Ty::type_reference(arena(&ret), "Promise", std::iter::empty()),
        );
    }
}
