use super::*;
use crate::checker::{Checker, NodeRef, SymbolRef};
use crate::checker_impl::UNDEFINED_IDENT;
use crate::mapper::TypeMapper;
use crate::program::ProgramHost;
use oxc_allocator::Allocator;
use oxc_ast::{
    AstKind,
    ast::{BigintBase, NumberBase},
};
use oxc_str::Ident;
use rustc_hash::FxHashMap;
use std::{
    borrow::Cow,
    path::{Path, PathBuf},
};

struct TestProgramHost {
    cwd: PathBuf,
    files: FxHashMap<PathBuf, String>,
}

impl TestProgramHost {
    fn new(cwd: impl Into<PathBuf>) -> Self {
        Self {
            cwd: cwd.into(),
            files: FxHashMap::default(),
        }
    }

    fn add_file(mut self, path: impl AsRef<Path>, source_text: &str) -> Self {
        let path = self.canonicalize_path(path.as_ref());
        self.files.insert(path, source_text.to_string());
        self
    }
}

impl program::ProgramHost for TestProgramHost {
    fn read_source(&self, path: &Path) -> program::ProgramStoreResult<Cow<'_, str>> {
        self.files
            .get(&self.canonicalize_path(path))
            .map(|source_text| Cow::Borrowed(source_text.as_str()))
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

fn parse_and_check_source<'a>(allocator: &'a Allocator, source_text: &str) -> ParseAndCheck<'a> {
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

fn checker<'a, 'store>(ret: &'store ParseAndCheck<'a>) -> Checker<'a, 'store> {
    Checker::with_arena(&ret.store, ret.arena)
}

fn type_string<'a>(ret: &ParseAndCheck<'a>, ty: Ty<'a>) -> String {
    checker(ret).to_type_string(ty)
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
            if let AstKind::Function(func) = semantic.nodes().kind(scoping.get_node_id(*scope_id)) {
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
                Some(type_string(
                    ret,
                    checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)),
                ))
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
                Some(type_string(
                    ret,
                    checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)),
                ))
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
            AstKind::IdentifierReference(identifier) if identifier.name == Ident::from(name) => {
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

fn assert_type_eq<'a, T>(arena: CheckerArena<'a>, left: &T, right: &T)
where
    T: TestTypeIdentity<'a> + std::fmt::Debug,
{
    assert!(
        left.is_identical_to(right, arena),
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

    let mut by_id = FxHashMap::default();
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
            type_string(&ret, checker.get_type_of_symbol(value_symbol)),
            constructor_type
        );
    }
}

#[test]
fn interface_symbol_has_named_declared_type() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
        interface Box<T = number> { value: T }
        ",
    );
    let checker = checker(&ret);
    let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
    let interface_node_id = semantic
        .nodes()
        .iter_enumerated()
        .find_map(|(node_id, node)| {
            matches!(node.kind(), AstKind::TSInterfaceDeclaration(_)).then_some(node_id)
        })
        .unwrap();
    let identifier_node_id = semantic
        .nodes()
        .iter_enumerated()
        .find_map(|(node_id, node)| match node.kind() {
            AstKind::BindingIdentifier(identifier)
                if identifier.name == Ident::from("Box")
                    && matches!(
                        semantic.nodes().parent_kind(node_id),
                        AstKind::TSInterfaceDeclaration(_)
                    ) =>
            {
                Some(node_id)
            }
            _ => None,
        })
        .unwrap();
    let interface_node = NodeRef::new(ret.program_id, interface_node_id);
    let identifier_node = NodeRef::new(ret.program_id, identifier_node_id);
    let symbol = checker.get_symbol_at_location(identifier_node).unwrap();

    assert_eq!(checker.get_type_at_location(interface_node), Ty::any());
    assert_eq!(checker.get_type_at_location(identifier_node), Ty::any());
    assert_eq!(
        type_string(&ret, checker.get_declared_type_of_symbol(symbol)),
        "Box<T>"
    );
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
        type_string(
            &ret,
            checker.get_type_at_location(NodeRef::new(ret.program_id, alias_name_node)),
        ),
        "((value: string) => number) | { accept(value: string): number; }"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "nodeFilterValue")),
        "{ readonly VALUE: 1; }"
    );
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
    let TyKind::Array(array) = checker.arena.ty_kind(ty) else {
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
    assert_eq!(type_string(&ret, ty), "Base64URLString[]");
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
            checker.get_type_at_location(NodeRef::new(ret.program_id, parameter_binding_node_id,)),
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
fn without_default_lib_has_no_global_type_symbols() {
    let allocator = Allocator::default();
    let host = TestProgramHost::new("/project").add_file("/project/main.ts", "const x = 1;");
    let store = program::ProgramStoreBuilder::new(&allocator, host)
        .add_root_file("/project/main.ts")
        .without_default_lib()
        .build()
        .unwrap();
    let program_id = store.id_for_path(Path::new("/project/main.ts")).unwrap();
    let checker = Checker::new(&store);

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
    let checker = Checker::new(&store);
    let scoping = store.entry(program_id).unwrap().semantic().scoping();
    let value_symbol_id = scoping.get_root_binding(Ident::from("value")).unwrap();

    assert!(
        checker
            .get_type_symbol_for_name(program_id, "Shared")
            .is_some()
    );
    assert_eq!(
        checker.to_type_string(
            checker.get_type_of_symbol(SymbolRef::new(program_id, value_symbol_id))
        ),
        "Shared"
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
        .map(|ty| type_string(&ret, ty))
        .collect::<Vec<_>>();
    let expected = "{ (message: any, targetOrigin: string, transfer?: Transferable[]): void; (message: any, options?: WindowPostMessageOptions): void; }";

    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "bare")),
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

    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "direct"),
        &Ty::number(),
    );
    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "computed"),
        &Ty::number(),
    );
    let excluded = get_global_symbol_type(&ret, "excluded");
    assert_eq!(
        excluded.error_kind(arena),
        Some(TypeErrorKind::UnresolvedMember)
    );
    assert_eq!(type_string(&ret, excluded), "any");
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "selfReference")),
        "typeof globalThis",
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "GlobalKeys")),
        "keyof typeof globalThis",
    );
    assert_type_eq(
        arena,
        &get_type_alias_type(&ret, "HasObjectProperty"),
        &Ty::boolean_true(),
    );
    assert_type_eq(
        arena,
        &get_type_alias_type(&ret, "IndexedObjectProperty"),
        &Ty::number(),
    );
    assert_type_eq(
        arena,
        &get_type_alias_type(&ret, "MappedObjectProperty"),
        &Ty::number(),
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "MappedSelfReference")),
        "typeof globalThis",
    );

    let global_this = get_global_symbol_type(&ret, "selfReference");
    let checker = checker(&ret);
    assert!(checker.is_assignable_to(
        global_this,
        arena.object([Ty::property(arena.str("objectProperty"), Ty::number())],),
    ));
    assert!(!checker.is_assignable_to(
        global_this,
        arena.object([Ty::property(arena.str("lexicalBinding"), Ty::string())],),
    ));
}

#[test]
fn global_this_conditional_matches_nested_global_value_property() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        r#"
        interface SymbolConstructor {
            readonly metadata: unique symbol;
        }
        type HasMetadata = typeof globalThis extends {
            Symbol: { readonly metadata: symbol };
        } ? true : false;
        "#,
    );

    assert_type_eq(
        arena(&ret),
        &get_type_alias_type(&ret, "HasMetadata"),
        &Ty::boolean_true(),
    );
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
    assert_eq!(type_string(&ret, leaked), "any");
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
        type_string(&ret, checker.get_type_of_symbol(symbol))
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
        ret.arena.ty_kind(declaration_type),
        types::TyKind::TypeReference(reference) if reference.target.is_some()
    ));
    let types::TyKind::Union(union) = ret.arena.ty_kind(members_type) else {
        panic!("expected enum member union");
    };
    assert_eq!(union.types.len(), 2);
    assert_eq!(union.types[0], declaration_type);
    assert_eq!(
        union
            .types
            .iter()
            .map(|ty| type_string(&ret, *ty))
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
    assert_eq!(type_string(&ret, member_types[0]), "E.A");
    assert_eq!(type_string(&ret, member_types[1]), "E.A");
    let checker = checker(&ret);
    assert!(!checker.is_assignable_to(member_types[0], member_types[1]));
    assert!(!checker.is_assignable_to(member_types[1], member_types[0]));
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
        &reference_types[0],
        &arena(&ret).union([Ty::string(), Ty::undefined()]),
    );
    assert_eq!(reference_types[1], Ty::string());
    assert_type_eq(
        ret.arena,
        &reference_types[2],
        &arena(&ret).union([Ty::string(), Ty::undefined()]),
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
        &reference_types[0],
        &arena(&ret).union([Ty::string(), Ty::number(), Ty::boolean()]),
    );
    assert_eq!(reference_types[1], Ty::string());
    assert_type_eq(
        ret.arena,
        &reference_types[2],
        &arena(&ret).union([Ty::number(), Ty::boolean()]),
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
            .map(|ty| type_string(&ret, ty))
            .collect::<Vec<_>>(),
        vec!["unknown".to_string(), "Action<string>".to_string()]
    );
    assert_eq!(
        get_identifier_reference_types(&ret, "baseValue")
            .into_iter()
            .map(|ty| type_string(&ret, ty))
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
            .map(|ty| type_string(&ret, ty))
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
        &get_global_symbol_type(&ret, "z"),
        &arena.union([Ty::string(), Ty::undefined()]),
    );
    assert_type_eq(
        arena,
        &get_identifier_reference_types(&ret, "y"),
        &vec![
            arena.union([Ty::string(), Ty::number(), Ty::boolean()]),
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
        type_string(&ret, get_global_symbol_type(&ret, "msg")),
        "\"something\" | \"arg = something\""
    );
    assert_eq!(
        get_identifier_reference_types(&ret, "arg")
            .into_iter()
            .map(|ty| type_string(&ret, ty))
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
        type_string(&ret, get_global_symbol_type(&ret, "msg")),
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
        type_string(&ret, get_first_symbol_type(&ret, "value")),
        "TData | (TData & ({} | null))"
    );
    assert_eq!(
        get_identifier_reference_types(&ret, "previous")
            .into_iter()
            .map(|ty| type_string(&ret, ty))
            .collect::<Vec<_>>(),
        vec![
            "TData | undefined".to_string(),
            "TData & ({} | null)".to_string(),
        ]
    );
}

#[test]
fn flow_narrows_reversed_null_equality_conditional_expression_arms() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    declare const value: string | null;
    const whenNull = null === value ? value : '';
    const whenString = null !== value ? value : '';
    ",
    );
    let arena = arena(&ret);

    assert_type_eq(
        arena,
        &get_identifier_reference_types(&ret, "value"),
        &vec![
            arena.union([Ty::string(), Ty::null()]),
            Ty::null(),
            arena.union([Ty::string(), Ty::null()]),
            Ty::string(),
        ],
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
        &reference_types[0],
        &arena(&ret).union([Ty::string(), Ty::number()]),
    );
    assert_eq!(reference_types[1], Ty::string());
    assert_eq!(reference_types[2], Ty::number());
}

#[test]
fn flow_compatible_assignment_preserves_previous_narrowing() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    let value: string | number;
    if (typeof value === 'string') {
        value = 'next';
        value;
    }
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types.len(), 3);
    assert_eq!(reference_types[1], Ty::string());
    assert_eq!(reference_types[2], Ty::string());
}

#[test]
fn flow_direct_assignment_updates_current_type() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    let value: string | number;
    value = 1;
    value;
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types.len(), 2);
    assert_type_eq(
        ret.arena,
        &reference_types[0],
        &arena(&ret).union([Ty::string(), Ty::number()]),
    );
    assert_eq!(reference_types[1], Ty::number());
}

#[test]
fn flow_self_referential_assignment_reads_pre_write_type() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    let value: number | undefined;
    value = +value;
    value;
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types.len(), 3);
    assert_type_eq(
        ret.arena,
        &reference_types[1],
        &arena(&ret).union([Ty::number(), Ty::undefined()]),
    );
    assert_eq!(reference_types[2], Ty::number());
}

#[test]
fn flow_self_referential_call_assignment_terminates() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    function next(value: any): number { return 1; }
    let value: any = 0;
    value = next(value);
    value = next(value);
    value;
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types.len(), 5);
    assert_eq!(reference_types[3], Ty::number());
    assert_eq!(reference_types[4], Ty::number());
}

#[test]
fn flow_merges_loop_carried_assignments_from_pre_loop_default() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    function test() {
        let value: any;
        value = 1;
        for (let index = 0; index < 1; index += 1) {
            value;
            value = 2;
        }
    }
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types.len(), 3);
    assert_eq!(type_string(&ret, reference_types[1]), "number");
}

#[test]
fn flow_for_in_body_does_not_reapply_null_assignment() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    var values = null;
    for (var key in values) {
        values[key];
    }
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "values");
    assert_eq!(reference_types.len(), 2);
    assert!(reference_types[1].is_any_like(ret.arena));
}

#[test]
fn structural_property_lookup_stops_on_unchanged_conditional_expansion() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    type Enum = Record<string, string | number>;
    type TypeMap<E extends Enum> = {
        [key in E[keyof E]]: number | boolean | string | number[]
    };
    class BufferPool<E extends Enum, M extends TypeMap<E>> {
        setArray<K extends E[keyof E]>(array: Extract<M[K], ArrayLike<any>>) {
            array.length;
        }
    }
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "array");
    assert_eq!(reference_types.len(), 1);
    assert_eq!(
        type_string(&ret, reference_types[0]),
        "Extract<M[K], ArrayLike<any>>"
    );
}

#[test]
fn flow_assignment_does_not_refine_later_compound_write_target() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    let value: any = 0;
    value = 1;
    value += 2;
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types.len(), 2);
    assert_eq!(reference_types[0], Ty::any());
    assert_eq!(reference_types[1], Ty::any());
}

#[test]
fn flow_applies_nested_branch_effects_in_order() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    declare const value: string | number | undefined;
    if (value) {
        if (typeof value === 'string') {
            value;
        }
    }
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types.len(), 3);
    assert_type_eq(
        ret.arena,
        &reference_types[1],
        &arena(&ret).union([Ty::string(), Ty::number()]),
    );
    assert_eq!(reference_types[2], Ty::string());
}

#[test]
fn flow_stops_at_control_flow_graph_depth_limit() {
    let allocator = Allocator::default();
    let mut source = String::from("declare const value: string | undefined;\n");
    for _ in 0..=crate::limits::CONTROL_FLOW_GRAPH_MAX_DEPTH {
        source.push_str("if (value) {\n");
    }
    source.push_str("value;\n");
    for _ in 0..=crate::limits::CONTROL_FLOW_GRAPH_MAX_DEPTH {
        source.push_str("}\n");
    }
    let ret = parse_and_check_source(&allocator, &source);
    let checker = checker(&ret);
    let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
    let node_id = semantic
        .nodes()
        .iter_enumerated()
        .filter_map(|(node_id, node)| match node.kind() {
            AstKind::IdentifierReference(identifier) if identifier.name == Ident::from("value") => {
                Some(node_id)
            }
            _ => None,
        })
        .last()
        .unwrap();

    let ty = checker.get_type_at_location(NodeRef::new(ret.program_id, node_id));

    assert_eq!(
        ty.error_kind(ret.arena),
        Some(TypeErrorKind::ControlFlowGraphDepthExceeded),
    );
}

#[test]
fn evolving_array_disables_flow_analysis_at_depth_limit() {
    let allocator = Allocator::default();
    let mut source = String::from("const data = [];\n");
    for _ in 0..crate::limits::CONTROL_FLOW_GRAPH_MAX_DEPTH {
        source.push_str("data[0] = 0;\n");
    }
    source.push_str("data[0] = 0;\ndata;\n");
    let ret = parse_and_check_source(&allocator, &source);
    let reference_types = get_identifier_reference_types(&ret, "data");

    assert!(
        reference_types[reference_types.len() - 3]
            .array_element_type(ret.arena)
            .is_some()
    );
    assert_eq!(
        reference_types[reference_types.len() - 2].error_kind(ret.arena),
        Some(TypeErrorKind::ControlFlowGraphDepthExceeded),
    );
    assert_eq!(
        reference_types.last().unwrap().error_kind(ret.arena),
        Some(TypeErrorKind::ControlFlowGraphDepthExceeded),
    );
}

#[test]
fn flow_depth_limit_only_disables_the_containing_function() {
    let allocator = Allocator::default();
    let mut source = String::from("function inner() {\nconst data = [];\n");
    for _ in 0..crate::limits::CONTROL_FLOW_GRAPH_MAX_DEPTH {
        source.push_str("data[0] = 0;\n");
    }
    source.push_str("data[0] = 0;\ndata;\n}\nconst outer = [];\nouter[0] = 0;\nouter;\n");
    let ret = parse_and_check_source(&allocator, &source);

    let inner_types = get_identifier_reference_types(&ret, "data");
    assert_eq!(
        inner_types.last().unwrap().error_kind(ret.arena),
        Some(TypeErrorKind::ControlFlowGraphDepthExceeded),
    );
    let outer_types = get_identifier_reference_types(&ret, "outer");
    assert!(outer_types.iter().all(|ty| !ty.is_error(ret.arena)));
    assert!(
        outer_types
            .last()
            .unwrap()
            .array_element_type(ret.arena)
            .is_some()
    );
}

#[test]
fn flow_narrows_logical_expression_rhs() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    declare const value: string | undefined;
    const result = value && value;
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types.len(), 2);
    assert_type_eq(
        ret.arena,
        &reference_types[0],
        &arena(&ret).union([Ty::string(), Ty::undefined()]),
    );
    assert_eq!(reference_types[1], Ty::string());
}

#[test]
fn flow_does_not_cross_deferred_closure_boundary() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    declare const value: string | undefined;
    if (value) {
        const read = () => value;
    }
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types.len(), 2);
    for ty in reference_types {
        assert_type_eq(
            ret.arena,
            &ty,
            &arena(&ret).union([Ty::string(), Ty::undefined()]),
        );
    }
}

#[test]
fn flow_ignores_write_in_sibling_branch() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    let value: string | undefined;
    declare const condition: boolean;
    if (condition && value) {
        value;
    } else {
        value = undefined;
    }
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_eq!(reference_types[1], Ty::string());
}

#[test]
fn flow_conservatively_invalidates_narrow_after_nested_write() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    let value: string | undefined;
    declare const condition: boolean;
    if (value) {
        if (condition) {
            value = undefined;
        }
        value;
    }
    ",
    );

    let reference_types = get_identifier_reference_types(&ret, "value");
    assert_type_eq(
        ret.arena,
        reference_types.last().unwrap(),
        &arena(&ret).union([Ty::string(), Ty::undefined()]),
    );
}

#[test]
fn flow_narrows_optional_static_member_in_true_branch() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    declare const container: { value: string | undefined };
    if (container?.value) {
        container.value;
    }
    ",
    );

    let member_types = get_static_member_expression_types(&ret, "value");
    assert_eq!(member_types.len(), 2);
    assert_eq!(member_types[1], Ty::string());
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
        &get_global_symbol_type(&ret, "before"),
        &arena.array(Ty::any()),
    );
    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "afterPush"),
        &arena.array(Ty::number()),
    );
    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "afterWrite"),
        &arena.array(arena.union([Ty::number(), Ty::string()])),
    );
    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "afterReset"),
        &arena.array(Ty::boolean()),
    );
}

#[test]
fn flow_evolving_array_mutation_target_stays_auto_array() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    let values = [];
    values.push(1);
    values.push('ready');
    const result = values;
    ",
    );
    let arena = arena(&ret);
    let reference_types = get_identifier_reference_types(&ret, "values");

    assert_eq!(reference_types.len(), 3);
    assert_type_eq(arena, &reference_types[0], &arena.array(Ty::any()));
    assert_type_eq(arena, &reference_types[1], &arena.array(Ty::any()));
    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "result"),
        &arena.array(arena.union([Ty::number(), Ty::string()])),
    );
}

#[test]
fn flow_evolving_array_ignores_mutation_in_sibling_branch() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "
    let values = [];
    declare const condition: boolean;
    if (condition) {
        values.push(1);
    } else {
        const untouched = values;
    }
    ",
    );

    assert_type_eq(
        ret.arena,
        &get_first_symbol_type(&ret, "untouched"),
        &arena(&ret).array(Ty::any()),
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
    let error = arena.error(TypeErrorKind::UnresolvedType);

    assert!(error.is_error(arena));
    assert_eq!(error.error_kind(arena), Some(TypeErrorKind::UnresolvedType));
    assert_ne!(error, Ty::any());
    assert_eq!(type_string(&ret, error), "any");
    assert_eq!(error.enum_variant_name(arena), "TyError");
    assert!(checker.is_assignable_to(error, Ty::number()));
    assert!(checker.is_assignable_to(Ty::number(), error));
    assert!(checker.is_assignable_to(error, Ty::unknown()));
    assert!(!checker.is_assignable_to(error, Ty::never()));
    assert_eq!(arena.union([error, Ty::string()]), error);
    assert_eq!(arena.intersection([error, Ty::string()]), error);
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
    assert_eq!(type_string(&ret, value_type), "any");
}

#[test]
fn intersection_with_any_reduces_to_any() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(&allocator, "");
    let arena = arena(&ret);
    let literal = arena.string_literal("foo");

    assert_eq!(arena.intersection([Ty::any(), literal]), Ty::any());
    assert_eq!(arena.intersection([literal, Ty::any()]), Ty::any());
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
        arena.number_literal(1.0, "1", NumberBase::Decimal),
        Ty::number()
    ));
    assert!(checker.is_assignable_to(arena.array(Ty::number()), arena.array(Ty::number())));

    let source = arena.object([
        Ty::property("x", Ty::number()),
        Ty::property("y", Ty::string()),
    ]);
    let target = arena.object([Ty::property("x", Ty::number())]);

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
        arena.function(vec![], vec![], Ty::string()),
        arena.function(vec![], vec![], Ty::any())
    ));

    // Regression test: Check that thenable is assignable to an intersection type
    let thenable = arena.object([Ty::property(
        "then",
        arena.function(vec![], vec![], Ty::any()),
    )]);
    let intersection = arena.intersection([Ty::primitive_object(), thenable]);
    assert!(checker.is_assignable_to(thenable, intersection));
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
        type_string(&ret, get_global_symbol_type(&ret, "streamedQuery")),
        "<TQueryFnData, TData>({ streamFn, refetchMode, reducer, initialValue, }: StreamedQueryParams<TQueryFnData, TData>) => TData"
    );
    assert_eq!(
        type_string(
            &ret,
            get_symbol_type_in_function(&ret, "streamedQuery", "streamFn")
        ),
        "(context: TQueryFnData) => TQueryFnData"
    );
    assert_eq!(
        type_string(
            &ret,
            get_symbol_type_in_function(&ret, "streamedQuery", "refetchMode")
        ),
        "\"append\" | \"reset\" | \"replace\""
    );
    assert_eq!(
        type_string(
            &ret,
            get_symbol_type_in_function(&ret, "streamedQuery", "reducer")
        ),
        "(acc: TData, chunk: TQueryFnData) => TData"
    );
    assert_eq!(
        type_string(
            &ret,
            get_symbol_type_in_function(&ret, "streamedQuery", "initialValue"),
        ),
        "TData"
    );
    assert_type_eq(
        ret.arena,
        &get_first_symbol_type(&ret, "items"),
        &arena(&ret).type_reference("TData", std::iter::empty()),
    );
    assert_type_eq(
        ret.arena,
        &get_first_symbol_type(&ret, "chunk"),
        &arena(&ret).type_reference("TQueryFnData", std::iter::empty()),
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
    let todo_type = arena.type_reference("Todo", std::iter::empty());
    let infinite_data_type = arena.type_reference("InfiniteData", [todo_type, Ty::number()]);

    assert_type_eq(
        arena,
        &get_first_symbol_type(&ret, "data"),
        &infinite_data_type,
    );
    assert_type_eq(arena, &get_first_symbol_type(&ret, "todo"), &todo_type);
    assert_eq!(
        type_string(&ret, get_object_property_types(&ret, "reducer")[0]),
        "(data: InfiniteData<Todo, number>, todo: Todo) => { pages: Todo[]; pageParams: number[]; }"
    );
    assert!(contains_type(
        arena,
        &get_object_property_types(&ret, "pages"),
        arena.array(todo_type),
    ));
    assert!(contains_type(
        arena,
        &get_object_property_types(&ret, "pages"),
        arena.array(Ty::never()),
    ));
    assert!(contains_type(
        arena,
        &get_object_property_types(&ret, "pageParams"),
        arena.array(Ty::never()),
    ));
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
        type_string(&ret, get_first_symbol_type(&ret, "context")),
        "{ queryKey: TQueryKey; pageParam?: unknown; }"
    );
    assert_eq!(
        type_string(
            &ret,
            get_symbol_type_in_function(&ret, "useParams", "streamFn")
        ),
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
        type_string(&ret, get_global_symbol_type(&ret, "box")),
        "<T>(value: T) => Box<T>"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "from")),
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
        type_string(&ret, get_global_symbol_type(&ret, "streamedQuery")),
        "<TQueryFnData = unknown, TData = TQueryFnData[], TQueryKey extends QueryKey = readonly unknown[]>({ streamFn, initialValue, }: StreamedQueryParams<TQueryFnData, TData, TQueryKey>) => QueryFunction<TData, TQueryKey>"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "QueryMeta")),
        "{ [x: string]: unknown; }"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "InferDataFromTag")),
        "TTaggedQueryKey extends { [dataTagSymbol]: infer TaggedValue; [dataTagErrorSymbol]: unknown; } ? TaggedValue : TQueryFnData"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "TaggedTodoData")),
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
        type_string(&ret, get_first_symbol_type(&ret, "signalLessContext")),
        "OmitKeyof<{ client: QueryClient; queryKey: TQueryKey; signal: AbortSignal; meta: QueryMeta | undefined; pageParam?: unknown; direction?: unknown; }, \"signal\">"
    );
    assert_eq!(
        type_string(&ret, get_first_symbol_type(&ret, "meta")),
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
        type_string(&ret, get_global_symbol_type(&ret, "dataTagSymbol")),
        "unique symbol"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "aliasValue")),
        "typeof dataTagSymbol"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "tagged")),
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
        type_string(&ret, get_type_alias_type(&ret, "UnsetMarker")),
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
    let checker = Checker::new(&store);
    let symbol_id = store
        .entry(program_id)
        .unwrap()
        .semantic()
        .scoping()
        .get_root_binding(Ident::from("values"))
        .unwrap();

    assert_type_eq(
        checker.arena,
        &checker.get_type_of_symbol(SymbolRef::new(program_id, symbol_id)),
        &checker.arena.type_reference("Array", [Ty::number()]),
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

    let TyKind::Tuple(t13) = ret.arena.ty_kind(get_type_alias_type(&ret, "T13")) else {
        panic!("expected T13 to remain a tuple");
    };
    assert_eq!(t13.elements.len(), 8192);
    let TyKind::Tuple(a13) = ret.arena.ty_kind(get_global_symbol_type(&ret, "a13")) else {
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
        assert_eq!(type_string(&ret, ty), "any");
    }

    let tuple_9999 = ret
        .arena
        .tuple(vec![TupleElement::Regular(Ty::any()); 9999]);
    let TyKind::Tuple(tuple) = ret
        .arena
        .ty_kind(ret.arena.tuple(vec![TupleElement::Rest(tuple_9999)]))
    else {
        panic!("expected a 9,999-element spread to remain a tuple");
    };
    assert_eq!(tuple.elements.len(), 9999);
    let oversized = ret.arena.tuple(vec![
        TupleElement::Regular(Ty::any()),
        TupleElement::Rest(tuple_9999),
    ]);
    assert_eq!(
        oversized.error_kind(ret.arena),
        Some(TypeErrorKind::TupleSizeExceeded)
    );
    assert_eq!(type_string(&ret, oversized), "any");
}

#[test]
fn conditional_infer_extracts_template_literal_segments() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        r#"
    type Whole = "user" extends `${infer K}` ? K : never;
    type Split = "user.name" extends `${infer K}.${infer R}` ? [K, R] : never;
    type LeadingEmpty = ".property" extends `${infer K}.${infer R}` ? [K, R] : never;
    type Adjacent = "abc" extends `${infer A}${infer B}` ? [A, B] : never;
    type NoMatch = "user" extends `prefix.${infer R}` ? R : "no";
    type User = { name: string; address: { city: string } };
    type UserKeys = keyof User;
    type NestedAlias = "user.name" extends `${infer K}.${infer R}`
        ? R extends UserKeys ? Pick<User, R> : never
        : never;
    type Tupleify<T extends string> = T extends `${infer K}.${infer R}`
        ? [K, ...Tupleify<R>]
        : [T];
    type TupleMatch = Tupleify<"user.address.city"> extends [infer P1, infer P2, infer P3]
        ? [P1, P2, P3]
        : never;
    type NestedTuple = Tupleify<"user.address.city"> extends [infer P1, infer P2, infer P3]
        ? P2 extends UserKeys
            ? P3 extends keyof User[P2] ? "yes" : "p3-no"
            : "p2-no"
        : "tuple-no";
    type KeyFormat = "jwk" | "pkcs8" | "raw" | "spki";
    type ExcludeValue<T, U> = T extends U ? never : T;
    type Formats = ExcludeValue<KeyFormat, "jwk">;
    "#,
    );

    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "Whole")),
        "\"user\""
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "Split")),
        "[\"user\", \"name\"]"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "LeadingEmpty")),
        "[\"\", \"property\"]"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "Adjacent")),
        "[\"a\", \"bc\"]"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "NoMatch")),
        "\"no\""
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "Tupleify")),
        "T extends `${infer K}.${infer R}` ? [K, ...Tupleify<R>] : [T]"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "TupleMatch")),
        "[\"user\", \"address\", \"city\"]"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "NestedTuple")),
        "\"yes\""
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "NestedAlias")),
        "{ name: string; }"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "Formats")),
        "\"pkcs8\" | \"raw\" | \"spki\""
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
        type_string(&ret, get_type_alias_type(&ret, "Value")),
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
        type_string(&ret, get_type_alias_type(&ret, "Value")),
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
        type_string(&ret, get_type_alias_type(&ret, "Value")),
        "\"yes\""
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "Deferred")),
        "unknown extends T ? IsAny<T, \"no\", \"yes\"> : \"no\""
    );
}

#[test]
fn conditional_infer_shadows_outer_type_parameter_substitution() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(&allocator, "const x = 1;");
    let checker = checker(&ret);
    let arena = arena(&ret);
    let outer_array = arena.array(Ty::string());
    let conditional = arena.conditional(
        arena.type_reference("T", []),
        arena.array(arena.infer(Ty::type_parameter("T", None, None))),
        arena.type_reference("T", []),
        Ty::never(),
        false,
    );
    let mapper = TypeMapper::single(arena.type_reference("T", []), outer_array);

    assert_eq!(checker.instantiate_type(conditional, &mapper), Ty::string());
}

#[test]
fn generic_instantiations_are_cached_by_target_and_mapper() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(&allocator, "const x = 1;");
    let checker = checker(&ret);
    let arena = arena(&ret);
    let target = arena.object([Ty::property("value", arena.type_reference("T", []))]);
    let first_mapper = TypeMapper::single(arena.type_reference("T", []), Ty::string());
    let second_mapper = TypeMapper::single(arena.type_reference("T", []), Ty::string());

    assert_eq!(
        checker.instantiate_type(target, &first_mapper),
        checker.instantiate_type(target, &second_mapper)
    );
}

#[test]
fn type_instantiation_resolves_structural_indexed_accesses() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(&allocator, "const x = 1;");
    let checker = checker(&ret);
    let arena = arena(&ret);
    let object_type = arena.object([Ty::property(
        "value",
        arena.type_reference("T", std::iter::empty()),
    )]);
    let indexed_access = arena.indexed_access(object_type, arena.string_literal("value"));
    let mapper = TypeMapper::single(arena.type_reference("T", std::iter::empty()), Ty::string());

    assert_eq!(
        checker.instantiate_type(indexed_access, &mapper),
        Ty::string()
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
    let TyKind::Tuple(small) = ret.arena.ty_kind(small_type) else {
        panic!("expected a tuple, got {}", type_string(&ret, small_type));
    };
    assert_eq!(small.elements.len(), 4);
    let value = get_type_alias_type(&ret, "Value");
    assert_eq!(
        value.error_kind(ret.arena),
        Some(TypeErrorKind::TypeInstantiationDepthExceeded)
    );
    assert_eq!(type_string(&ret, value), "any");
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
    assert!(type_string(&ret, ty).contains("ParseManyWhitespace<R0>"));
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
    let TyKind::Tuple(tuple) = ret.arena.ty_kind(promised) else {
        panic!(
            "expected an empty tuple, got {}",
            type_string(&ret, promised)
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
        type_string(&ret, get_type_alias_type(&ret, "OmitKeyof")),
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
        type_string(&ret, get_type_alias_type(&ret, "Value")),
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
        type_string(&ret, get_type_alias_type(&ret, "PrimitiveAliases")),
        "string"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "LiteralAliasWithPrimitive")),
        "string"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "LiteralAliases")),
        "1 | 2"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "NamedUnionAlias")),
        "BooleanLogicExpression | \"true\" | \"false\""
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "ObjectAlias")),
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
        type_string(&ret, get_type_alias_type(&ret, "Params")),
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
        type_string(&ret, get_type_alias_type(&ret, "OptionalFlat")),
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
        type_string(&ret, get_type_alias_type(&ret, "Deferred")),
        "\"requireExactProps\" extends keyof Options ? Options[\"requireExactProps\"] : false"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "DeferredWrapped")),
        "\"requireExactProps\" extends keyof Options ? Wrapper<Options[keyof Options & \"requireExactProps\"]> : false"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "Concrete")),
        "true"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "Outer")),
        "(\"requireExactProps\" extends keyof Options ? Options[\"requireExactProps\"] : false) extends true ? \"yes\" : \"no\""
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "OuterViaParameter")),
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
        &get_global_symbol_type(&ret, "value"),
        &arena(&ret).union([Ty::boolean(), Ty::number()]),
    );
}

#[test]
fn structural_property_lookup_uses_compatible_index_signatures() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        r#"
    declare const literal: { [key: "foo"]: number };
    declare const union: { [key: "foo" | "bar"]: boolean };
    declare const string: { [key: string]: bigint };

    const literalValue = literal.foo;
    const unionValue = union.bar;
    const stringValue = string.anything;
    "#,
    );

    assert_eq!(get_global_symbol_type(&ret, "literalValue"), Ty::number());
    assert_eq!(get_global_symbol_type(&ret, "unionValue"), Ty::boolean());
    assert_eq!(get_global_symbol_type(&ret, "stringValue"), Ty::bigint());
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
        .collect::<FxHashMap<_, _>>();

    assert_eq!(expression_types.len(), 9);
    assert_type_eq(
        ret.arena,
        &expression_types["numeric"],
        &arena(&ret).number_literal(42.0, "42", NumberBase::Decimal),
    );
    assert_eq!(type_string(&ret, expression_types["bigint"]), "1n");
    assert_eq!(
        expression_types["string"],
        arena(&ret).string_literal("hello")
    );
    assert_eq!(expression_types["boolean"], Ty::boolean_true());
    assert_eq!(expression_types["call"], Ty::number());
    assert!(expression_types.values().all(|ty| !ty.is_none()));
}

#[test]
fn bigint_literal_types_store_parsed_value_and_source_metadata() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        "const decimal = 1n; const hex = 0x2n; const zero = 0b0_0n; const octal = 0o1n;",
    );
    let checker = checker(&ret);
    let semantic = ret.store.entry(ret.program_id).unwrap().semantic();
    let literal_types = semantic
        .nodes()
        .iter_enumerated()
        .filter_map(|(node_id, node)| match node.kind() {
            AstKind::BigIntLiteral(_) => {
                Some(checker.get_type_at_location(NodeRef::new(ret.program_id, node_id)))
            }
            _ => None,
        })
        .collect::<Vec<_>>();

    assert_eq!(literal_types.len(), 4);
    assert_eq!(literal_types[0], literal_types[3]);

    let TyKind::BigIntLiteral(decimal) = ret.arena.ty_kind(literal_types[0]) else {
        panic!("expected decimal bigint literal type")
    };
    assert_eq!(decimal.value, "1");
    assert_eq!(decimal.raw.as_ref().map(oxc_str::Str::as_str), Some("1n"));
    assert_eq!(decimal.base, BigintBase::Decimal);

    let TyKind::BigIntLiteral(hex) = ret.arena.ty_kind(literal_types[1]) else {
        panic!("expected hexadecimal bigint literal type")
    };
    assert_eq!(hex.value, "2");
    assert_eq!(hex.raw.as_ref().map(oxc_str::Str::as_str), Some("0x2n"));
    assert_eq!(hex.base, BigintBase::Hex);

    let TyKind::BigIntLiteral(zero) = ret.arena.ty_kind(literal_types[2]) else {
        panic!("expected binary bigint literal type")
    };
    assert_eq!(zero.value, "0");
    assert_eq!(zero.raw.as_ref().map(oxc_str::Str::as_str), Some("0b0_0n"));
    assert_eq!(zero.base, BigintBase::Binary);
}

#[test]
fn type_strings_render_string_literals_with_double_quotes() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(&allocator, "");
    let arena = arena(&ret);

    assert_eq!(
        type_string(&ret, arena.string_literal("expects a string literal")),
        "\"expects a string literal\""
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
        type_string(&ret, get_global_symbol_type(&ret, "declarations")),
        "{ view: BufferView; maybeView?: BufferView; stream: Stream; iterable: LocalIterable<string>; explicitIterable: LocalIterable<string, any, any>; float: Float32Array<ArrayBufferLike>; values: number[] | Float32Array<ArrayBufferLike>; }"
    );
}

#[test]
fn generic_function_mapped_constraint_preserves_literal_inference() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        r#"
    declare function pick<Shape, Mask extends { [Key in keyof Shape]?: true }>(
        shape: Shape,
        mask: Mask,
    ): void;

    pick({ id: "", active: false }, { id: true, active: true });
    "#,
    );

    assert_eq!(
        get_object_property_types(&ret, "active"),
        vec![Ty::boolean(), Ty::boolean_true()]
    );
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
        &get_global_symbol_type(&ret, "value"),
        &arena(&ret).string_literal("ready"),
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
        &get_global_symbol_type(&ret, "result"),
        &arena(&ret).string_literal("ready"),
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
        type_string(&ret, get_global_symbol_type(&ret, "target")),
        "Box<number>"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "object")),
        "Box<number>"
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
        type_string(&ret, get_global_symbol_type(&ret, "unwrapped")),
        "Box<number>"
    );
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
fn optional_interface_method_signature_location_includes_undefined() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        r#"
    interface AccessorResult<This, Value> {
        get?(this: This): Value;
        set(this: This, value: Value): void;
    }
    "#,
    );

    assert_eq!(
        get_ts_method_signature_types(&ret, "get"),
        vec!["((this: This) => Value) | undefined".to_string()]
    );
    assert_eq!(
        get_ts_method_signature_types(&ret, "set"),
        vec!["(this: This, value: Value) => void".to_string()]
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
        .map(|ty| type_string(&ret, ty))
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
fn merged_namespace_interface_method_signatures_across_programs_use_overload_object_type() {
    let allocator = Allocator::default();
    let source = r#"
    declare namespace MergeSpace {
        interface Exception {
            getArg(exceptionTag: Tag, index: number): any;
        }
        interface Tag {}
    }
    "#;
    let host = TestProgramHost::new("/project")
        .add_file("/project/a.ts", source)
        .add_file("/project/b.ts", source);
    let store = program::ProgramStoreBuilder::new(&allocator, host)
        .add_root_file("/project/a.ts")
        .add_root_file("/project/b.ts")
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
        get_ts_method_signature_types(&ret, "getArg"),
        vec![
            "{ (exceptionTag: Tag, index: number): any; (exceptionTag: Tag, index: number): any; }"
                .to_string(),
        ]
    );
}

#[test]
fn namespace_interface_method_signatures_do_not_merge_across_external_modules() {
    let allocator = Allocator::default();
    let source = r#"
    export {};
    declare namespace MergeSpace {
        interface Exception {
            getArg(exceptionTag: Tag, index: number): any;
        }
        interface Tag {}
    }
    "#;
    let host = TestProgramHost::new("/project")
        .add_file("/project/a.ts", source)
        .add_file("/project/b.ts", source);
    let store = program::ProgramStoreBuilder::new(&allocator, host)
        .add_root_file("/project/a.ts")
        .add_root_file("/project/b.ts")
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
        get_ts_method_signature_types(&ret, "getArg"),
        vec!["(exceptionTag: Tag, index: number) => any".to_string()]
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
        type_string(&ret, get_global_symbol_type(&ret, "Err")),
        "typeof ErrImpl & (<T>() => T)"
    );
    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "e"),
        &arena.intersection([
            arena.object([
                Ty::property("new ()", arena.type_reference("ErrImpl", [Ty::number()])),
                Ty::property("prototype", arena.type_reference("ErrImpl", [Ty::any()])),
            ]),
            arena.function([], [], Ty::number()),
        ]),
    );
}

#[test]
fn classes_use_class_types_in_value_queries() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        r#"
    class C {
        static value = 1;
        instance = "value";
    }
    const ctor = C;
    const instance = new C();
    type Ctor = typeof C;
    "#,
    );
    let class_type = get_global_symbol_type(&ret, "C");
    let constructor_value_type = get_global_symbol_type(&ret, "ctor");
    let constructor_alias_type = get_global_symbol_type(&ret, "Ctor");

    assert_eq!(class_type.enum_variant_name(ret.arena), "TyClass");
    assert_eq!(
        constructor_value_type.enum_variant_name(ret.arena),
        "TyClass"
    );
    assert_eq!(
        constructor_alias_type.enum_variant_name(ret.arena),
        "TyClass"
    );
    assert_eq!(type_string(&ret, class_type), "typeof C");
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "instance")),
        "C"
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
        &get_global_symbol_type(&ret, "literalUnionResult"),
        &arena.union([
            arena.number_literal(2.0, "2", NumberBase::Decimal),
            arena.number_literal(1.0, "1", NumberBase::Decimal),
        ]),
    );
    assert_eq!(
        get_global_symbol_type(&ret, "nestedFunctionResult"),
        Ty::void()
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
        type_string(&ret, get_first_symbol_type(&ret, "syncValue")),
        "1 | 2"
    );
    assert_eq!(
        type_string(&ret, get_first_symbol_type(&ret, "asyncValue")),
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
        type_string(&ret, get_first_symbol_type(&ret, "value")),
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

    let spread_promise = type_string(&ret, get_first_symbol_type(&ret, "spreadPromise"));
    assert!(spread_promise.contains("then<TResult1, TResult2>"));
    assert!(spread_promise.contains("[Symbol.toStringTag]: string"));
    assert!(
        spread_promise
            .contains("finally(onfinally?: (() => void) | undefined | null): Promise<number>"),
        "{spread_promise}"
    );
    assert!(spread_promise.find("[Symbol.toStringTag]") < spread_promise.find("finally(onfinally"));
    let spread_map = type_string(&ret, get_first_symbol_type(&ret, "spreadMap"));
    assert!(spread_map.contains("set(key: string, value: number): Map<string, number>"));
    assert!(spread_map.contains("[Symbol.iterator](): MapIterator<[string, number]>"));
    assert!(spread_map.find("[Symbol.iterator]") < spread_map.find("entries()"));
    assert!(spread_map.find("values()") < spread_map.find("[Symbol.toStringTag]"));
    assert_eq!(
        type_string(&ret, get_first_symbol_type(&ret, "mapObject")),
        "{ [k: string]: number; }"
    );
    assert_eq!(
        type_string(&ret, get_first_symbol_type(&ret, "getObjectSpread")),
        "{ [x: string]: string; }"
    );
    assert_eq!(
        type_string(&ret, get_first_symbol_type(&ret, "characters")),
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
        type_string(
            &shadowed_ret,
            get_first_symbol_type(&shadowed_ret, "spreadPromise"),
        ),
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
    let spread_map = type_string(
        &augmented_ret,
        get_first_symbol_type(&augmented_ret, "spreadMap"),
    );
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
        type_string(&ret, get_first_symbol_type(&ret, "instanceSpread")),
        "{ value: number; }"
    );
    assert_eq!(
        type_string(&ret, get_first_symbol_type(&ret, "genericInstanceSpread")),
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
        assert_eq!(type_string(&ret, ty), "any");
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
        &get_global_symbol_type(&ret, "promise"),
        &arena.type_reference("Promise", [Ty::unknown()]),
    );
    assert_eq!(
        type_string(&ret, get_first_symbol_type(&ret, "resolve")),
        "(value: unknown) => void"
    );
    assert_eq!(
        type_string(&ret, get_first_symbol_type(&ret, "reject")),
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
        &get_global_symbol_type(&ret, "rejected"),
        &arena(&ret).type_reference("Promise", [Ty::never()]),
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
        type_string(&ret, get_global_symbol_type(&ret, "thenMethod")),
        "<TResult1, TResult2>(onfulfilled?: ((value: string) => TResult1 | PromiseLike<TResult1>) | null | undefined, onrejected?: ((reason: any) => TResult2 | PromiseLike<TResult2>) | null | undefined) => Promise<TResult1 | TResult2>"
    );
    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "thenResult"),
        &arena.type_reference("Promise", [Ty::void()]),
    );
    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "defaultThenResult"),
        &arena.type_reference("Promise", [Ty::string()]),
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "catchMethod")),
        "<TResult>(onrejected?: ((reason: any) => TResult | PromiseLike<TResult>) | null | undefined) => Promise<TResult>"
    );
    assert_type_eq(
        arena,
        &get_global_symbol_type(&ret, "catchResult"),
        &arena.type_reference("Promise", [Ty::void()]),
    );
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
        type_string(&ret, get_type_alias_type(&ret, "Value")),
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

    assert_eq!(type_string(&ret, get_type_alias_type(&ret, "T1")), "number");
    assert_eq!(type_string(&ret, get_type_alias_type(&ret, "T2")), "void");
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "arrayOfPromises")),
        "Promise<number>[]"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "all")),
        "Promise<void[]>"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "allTuple")),
        "Promise<[number, string]>"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "readonlyCopyOfTuple")),
        "readonly [number, string]"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "mutableCopyOfTuple")),
        "[number, string]"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "optionalCopyOfTuple")),
        "[(number | undefined)?, (string | undefined)?]"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "requiredCopyOfTuple")),
        "[number, string]"
    );
    assert_eq!(
        type_string(
            &ret,
            get_global_symbol_type(&ret, "requiredCopyOfOptionalUndefined")
        ),
        "[never]"
    );
    assert_eq!(
        type_string(
            &ret,
            get_global_symbol_type(&ret, "requiredCopyOfOptionalUnionUndefined"),
        ),
        "[number]"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "constructedAll")),
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
        type_string(&ret, get_type_alias_type(&ret, "Nullish")),
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
        type_string(&ret, get_type_alias_type(&ret, "StructuralThenable")),
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
        type_string(&ret, get_type_alias_type(&ret, "StructuralThenable")),
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
        type_string(&ret, get_type_alias_type(&ret, "Primitive")),
        "number"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "PlainObject")),
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
        type_string(&ret, get_type_alias_type(&ret, "StructuralThenable")),
        "string"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "NestedStructuralThenable")),
        "number"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "PromiseValue")),
        "string"
    );
    assert_eq!(
        type_string(&ret, get_type_alias_type(&ret, "NestedPromiseValue")),
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
        type_string(&ret, get_type_alias_type(&ret, "NonCallableThenArgument")),
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
        type_string(&ret, get_global_symbol_type(&ret, "returnsPromise")),
        "{ (): Promise<string>; (): Promise<string>; (): Promise<string>; }"
    );
}

#[test]
fn module_scoped_namespace_has_no_symbol_in_sibling_program() {
    let allocator = Allocator::default();
    let host = TestProgramHost::new("/project")
        .add_file(
            "/project/a.ts",
            "export {}; namespace moduleScoped { export const value = 1; }",
        )
        .add_file(
            "/project/b.ts",
            "export {}; const result = moduleScoped.value;",
        );
    let store = program::ProgramStoreBuilder::new(&allocator, host)
        .add_root_file("/project/a.ts")
        .add_root_file("/project/b.ts")
        .build()
        .unwrap();
    let program_id = store.id_for_path(Path::new("/project/b.ts")).unwrap();
    let arena = CheckerArena::new(store.allocator());
    let ret = ParseAndCheck {
        store,
        program_id,
        arena,
    };
    let checker = checker(&ret);
    let semantic = ret.store.entry(program_id).unwrap().semantic();
    let node_id = semantic
        .nodes()
        .iter_enumerated()
        .find_map(|(node_id, node)| {
            matches!(
                node.kind(),
                AstKind::IdentifierReference(identifier)
                    if identifier.name == Ident::from("moduleScoped")
            )
            .then_some(node_id)
        })
        .unwrap();
    let node = NodeRef::new(program_id, node_id);

    assert!(checker.get_symbol_at_location(node).is_none());
    assert_eq!(
        checker.get_type_at_location(node).error_kind(ret.arena),
        Some(TypeErrorKind::UnresolvedSymbol)
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
        type_string(&ret, get_global_symbol_type(&ret, "fn")),
        "<T = A>(x: T) => T"
    );
    assert_eq!(
        type_string(&ret, get_global_symbol_type(&ret, "foo")),
        "<T = A>(x?: T) => T"
    );
    assert_type_eq(
        ret.arena,
        &get_global_symbol_type(&ret, "fromDefault"),
        &arena(&ret).type_reference("A", std::iter::empty()),
    );
    assert_type_eq(
        ret.arena,
        &get_global_symbol_type(&ret, "fromInference"),
        &arena(&ret).type_reference("A", std::iter::empty()),
    );
    assert_eq!(
        get_global_symbol_type(&ret, "fromDependentDefault"),
        Ty::string()
    );
    assert_type_eq(
        ret.arena,
        &get_global_symbol_type(&ret, "unresolvedValue"),
        &arena(&ret).type_reference("T", std::iter::empty()),
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
        type_string(&ret, get_global_symbol_type(&ret, "source")),
        "{ <K extends keyof WindowEventMap>(type: K, listener: (this: Window, ev: WindowEventMap[K]) => any): void; }"
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
fn new_expression_infers_from_tuple_rest_arguments() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(
        &allocator,
        r#"
    declare const Factory: { new <T>(...args: [label: string, value: T]): T };

    const value = new Factory("answer", 42);
    "#,
    );

    assert_type_eq(
        ret.arena,
        &get_global_symbol_type(&ret, "value"),
        &arena(&ret).number_literal(42.0, "42", NumberBase::Decimal),
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
    assert_eq!(type_string(&ret, regex_lowercase), "any");
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
    assert_eq!(type_string(&ret, rec_value2), "any");
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
        &get_global_symbol_type(&ret, "userId"),
        &arena(&ret).union([Ty::number(), Ty::undefined()]),
    );
    assert_type_eq(
        ret.arena,
        &get_global_symbol_type(&ret, "userName"),
        &arena(&ret).union([Ty::string(), Ty::undefined()]),
    );
    assert_type_eq(
        ret.arena,
        &get_global_symbol_type(&ret, "userId2"),
        &arena(&ret).union([Ty::number(), Ty::undefined()]),
    );
    assert_type_eq(
        ret.arena,
        &get_global_symbol_type(&ret, "userName2"),
        &arena(&ret).union([Ty::string(), Ty::undefined()]),
    );
    assert_type_eq(
        ret.arena,
        &get_global_symbol_type(&ret, "optionalNestedArray"),
        &arena(&ret)
            .object([Ty::property("label", Ty::string())])
            .or_undefined(arena(&ret)),
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
        type_string(&ret, get_global_symbol_type(&ret, "foo")),
        "(a: string, b?: string, c?: number, ...d: number[]) => void"
    );
    let ty = get_global_symbol_type(&ret, "foo");
    let TyKind::Function(function) = ret.arena.ty_kind(ty) else {
        panic!("expected function type");
    };
    let rest_parameter = function.parameters[3];
    assert_eq!(rest_parameter.name, "d");
    assert!(rest_parameter.rest);
}

#[test]
fn test_get_global_type() {
    let allocator = Allocator::default();
    let ret = parse_and_check_source(&allocator, "");
    let checker = checker(&ret);

    // Now test things that should be in the global environment:
    assert_type_eq(
        ret.arena,
        &get_global_type(&ret, ret.program_id, "Promise"),
        &Some(arena(&ret).type_reference("Promise", std::iter::empty())),
    );
    assert_type_eq(
        ret.arena,
        &checker.get_global_promise_type(ret.program_id),
        &arena(&ret).type_reference("Promise", std::iter::empty()),
    );
}
