#![allow(dead_code, unused_imports)]
use oxc_ast::{
    AstKind,
    ast::{Expression, Program, TSType, TSTypeAnnotation, VariableDeclarator},
};
use oxc_index::nonmax::NonMaxU32;
use oxc_semantic::{AstNode, AstNodes, NodeId, Semantic, SemanticBuilder, SymbolId};
use oxc_span::GetSpan;
use oxc_str::Ident;
use std::cell::RefCell;

pub mod program;

// TODO: Make use of the same pattern in oxc_ast for ast node types
#[derive(Debug, PartialEq, Eq, Clone)]
enum Ty {
    None,
    Number,
    String,
    Boolean,
    Bigint,
    Undefined,
    Null,
    Any,
    Unknown,
}

impl Ty {
    /// Take a type annotation like `: number` and return the corresponding type. Returns no
    /// type if there is no type annotation.
    fn from_ts_type_annotation(type_annotation: Option<&TSTypeAnnotation<'_>>) -> Self {
        type_annotation.map_or(Self::Any, |type_annotation| {
            Self::from_ts_type(&type_annotation.type_annotation)
        })
    }

    /// Turns a declared type in the AST and turns it into an actual type.
    fn from_ts_type(t: &TSType<'_>) -> Self {
        match t {
            TSType::TSNumberKeyword(_) => Self::Number,
            TSType::TSStringKeyword(_) => Self::String,
            TSType::TSBooleanKeyword(_) => Self::Boolean,
            TSType::TSBigIntKeyword(_) => Self::Bigint,
            TSType::TSUndefinedKeyword(_) => Self::Undefined,
            TSType::TSNullKeyword(_) => Self::Null,
            TSType::TSAnyKeyword(_) => Self::Any,
            TSType::TSUnknownKeyword(_) => Self::Unknown,
            TSType::TSParenthesizedType(parenthesized) => {
                Self::from_ts_type(&parenthesized.type_annotation)
            }
            _ => Self::None,
        }
    }

    fn from_expression(expression: &Expression<'_>) -> Self {
        match expression {
            Expression::BooleanLiteral(_) => Self::Boolean,
            Expression::NumericLiteral(_) => Self::Number,
            Expression::BigIntLiteral(_) => Self::Bigint,
            Expression::StringLiteral(_) => Self::String,
            Expression::NullLiteral(_) => Self::Any,
            _ => Self::Any,
        }
    }
}

/*

type Signature struct {
    flags                    SignatureFlags
    minArgumentCount         int32
    resolvedMinArgumentCount int32
    declaration              *ast.Node
    typeParameters           []*Type
    parameters               []*ast.Symbol
    thisParameter            *ast.Symbol
    resolvedReturnType       *Type
    resolvedTypePredicate    *TypePredicate
    target                   *Signature
    mapper                   *TypeMapper
    isolatedSignatureType    *Type
    composite                *CompositeSignature
}

type Checker interface {
    CheckFile(ctx context.Context, file *SourceFile) []Diagnostic
    GetGlobalDiagnostics() []Diagnostic

    GetSymbolAtLocation(node *Node) *Symbol
    GetTypeAtLocation(node *Node) *Type
    GetTypeFromTypeNode(node *Node) *Type

    GetDeclaredTypeOfSymbol(symbol *Symbol) *Type
    GetTypeOfSymbol(symbol *Symbol) *Type
    GetTypeOfSymbolAtLocation(symbol *Symbol, location *Node) *Type

    GetPropertiesOfType(t *Type) []*Symbol
    GetPropertyOfType(t *Type, name string) *Symbol
    GetSignaturesOfType(t *Type, kind SignatureKind) []*Signature
    GetIndexInfosOfType(t *Type) []*IndexInfo

    IsAssignableTo(source, target *Type) bool
    TypeToString(t *Type, location *Node) string
    SymbolToString(s *Symbol, location *Node) string
}

*/

enum SignatureKind {
    Call,
    Construct,
}
struct Signature {}
struct IndexInfo {}

trait Checker {
    fn get_symbol_at_location(&self, node: NodeRef) -> Option<SymbolRef>;
    fn get_type_at_location(&self, node: NodeRef) -> Ty;
    // fn get_type_from_type_node(&self, type_node: NodeRef) -> Ty;
    fn get_declared_type_of_symbol(&self, sym: SymbolRef) -> Ty;
    fn get_type_of_symbol(&self, sym: SymbolRef) -> Ty;
    fn get_type_of_symbol_at_location(&self, node: NodeRef) -> Ty;
    fn get_properties_of_type(&self, t: Ty) -> Vec<SymbolRef>;
    fn get_property_of_type(&self, t: Ty, name: &str) -> Option<SymbolRef>;
    fn get_signatures_of_type(&self, t: Ty, kind: SignatureKind) -> Vec<Signature>;
    fn get_index_infos_of_type(&self, t: Ty) -> Vec<IndexInfo>;
    fn is_assignable_to(&self, source: Ty, target: Ty) -> bool;
    fn type_to_string(&self, t: Ty, location: NodeRef) -> String;
    fn symbol_to_string(&self, s: SymbolRef, location: NodeRef) -> String;
}

struct CheckerBuilder {}

impl CheckerBuilder {
    fn new() -> Self {
        Self {}
    }

    fn build<'a, 'store>(
        &self,
        store: &'store program::ProgramStore<'a>,
    ) -> CheckerReturn<'a, 'store> {
        CheckerReturn {
            store,
            resolving_symbols: RefCell::new(Vec::new()),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NodeRef {
    program_id: program::ProgramId,
    node_id: NodeId,
}

impl NodeRef {
    fn new(program_id: program::ProgramId, node_id: NodeId) -> Self {
        Self {
            program_id,
            node_id,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SymbolRef {
    program_id: program::ProgramId,
    symbol_id: SymbolId,
}

impl SymbolRef {
    fn new(program_id: program::ProgramId, symbol_id: SymbolId) -> Self {
        Self {
            program_id,
            symbol_id,
        }
    }
}

struct CheckerReturn<'a, 'store> {
    store: &'store program::ProgramStore<'a>,
    resolving_symbols: RefCell<Vec<SymbolRef>>,
}

impl<'a, 'store> CheckerReturn<'a, 'store> {
    #[inline]
    fn entry(&self, program_id: program::ProgramId) -> &program::ProgramEntry<'a> {
        self.store
            .entry(program_id)
            .expect("store-backed checker must reference a valid program")
    }

    #[inline]
    fn semantic(&self, program_id: program::ProgramId) -> &Semantic<'a> {
        self.entry(program_id).semantic()
    }

    #[inline]
    fn nodes(&self, program_id: program::ProgramId) -> &AstNodes<'a> {
        self.semantic(program_id).nodes()
    }

    #[inline]
    fn node_kind(&self, node: NodeRef) -> AstKind<'a> {
        self.nodes(node.program_id).kind(node.node_id)
    }

    fn get_type_of_expression(
        &self,
        program_id: program::ProgramId,
        expression: &Expression<'_>,
    ) -> Ty {
        match expression {
            Expression::Identifier(identifier) => identifier
                .reference_id
                .get()
                .and_then(|reference_id| {
                    self.semantic(program_id)
                        .scoping()
                        .get_reference(reference_id)
                        .symbol_id()
                })
                .map_or(Ty::Any, |symbol_id| {
                    self.get_type_of_symbol(SymbolRef::new(program_id, symbol_id))
                }),
            _ => Ty::from_expression(expression),
        }
    }

    fn get_type_of_import_symbol(&self, symbol: SymbolRef) -> Option<Ty> {
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        let declaration_ref = NodeRef::new(symbol.program_id, declaration);
        let AstKind::ImportSpecifier(specifier) = self.node_kind(declaration_ref) else {
            return None;
        };
        let AstKind::ImportDeclaration(import_declaration) =
            self.nodes(symbol.program_id).parent_kind(declaration)
        else {
            return None;
        };
        let imported_name = specifier.imported.name();
        let imported_program_id = self
            .store
            .resolved_module(symbol.program_id, import_declaration.source.value.as_str())?;
        let imported_entry = self.store.entry(imported_program_id)?;
        let imported_symbol_id = imported_entry
            .semantic()
            .scoping()
            .get_root_binding(Ident::from(imported_name.as_str()))?;

        Some(self.get_type_of_symbol(SymbolRef::new(imported_program_id, imported_symbol_id)))
    }
}

impl Checker for CheckerReturn<'_, '_> {
    fn get_symbol_at_location(&self, node: NodeRef) -> Option<SymbolRef> {
        match self.node_kind(node) {
            AstKind::BindingIdentifier(identifier) => identifier
                .symbol_id
                .get()
                .map(|symbol_id| SymbolRef::new(node.program_id, symbol_id)),
            AstKind::IdentifierReference(identifier) => {
                identifier.reference_id.get().and_then(|reference_id| {
                    self.semantic(node.program_id)
                        .scoping()
                        .get_reference(reference_id)
                        .symbol_id()
                        .map(|symbol_id| SymbolRef::new(node.program_id, symbol_id))
                })
            }
            _ => None,
        }
    }

    fn get_type_at_location(&self, node: NodeRef) -> Ty {
        self.get_symbol_at_location(node)
            .map_or(Ty::None, |sym| self.get_type_of_symbol(sym))
    }

    fn get_declared_type_of_symbol(&self, sym: SymbolRef) -> Ty {
        match self
            .semantic(sym.program_id)
            .symbol_declaration(sym.symbol_id)
            .kind()
        {
            AstKind::VariableDeclarator(declarator) => {
                Ty::from_ts_type_annotation(declarator.type_annotation.as_deref())
            }
            AstKind::FormalParameter(parameter) => {
                Ty::from_ts_type_annotation(parameter.type_annotation.as_deref())
            }
            AstKind::FormalParameterRest(parameter) => {
                Ty::from_ts_type_annotation(parameter.type_annotation.as_deref())
            }
            AstKind::CatchParameter(parameter) => {
                Ty::from_ts_type_annotation(parameter.type_annotation.as_deref())
            }
            AstKind::PropertyDefinition(property) => {
                Ty::from_ts_type_annotation(property.type_annotation.as_deref())
            }
            AstKind::AccessorProperty(property) => {
                Ty::from_ts_type_annotation(property.type_annotation.as_deref())
            }
            _ => Ty::None,
        }
    }

    fn get_type_of_symbol(&self, sym: SymbolRef) -> Ty {
        {
            let mut resolving_symbols = self.resolving_symbols.borrow_mut();
            if resolving_symbols.contains(&sym) {
                return Ty::Any;
            }
            resolving_symbols.push(sym);
        }

        let ty = if let Some(imported_type) = self.get_type_of_import_symbol(sym) {
            imported_type
        } else {
            match self
                .semantic(sym.program_id)
                .symbol_declaration(sym.symbol_id)
                .kind()
            {
                AstKind::VariableDeclarator(declarator) => {
                    if declarator.type_annotation.is_some() {
                        Ty::from_ts_type_annotation(declarator.type_annotation.as_deref())
                    } else {
                        declarator.init.as_ref().map_or(Ty::Any, |expression| {
                            self.get_type_of_expression(sym.program_id, expression)
                        })
                    }
                }
                _ => self.get_declared_type_of_symbol(sym),
            }
        };

        self.resolving_symbols.borrow_mut().pop();
        ty
    }

    fn get_type_of_symbol_at_location(&self, node: NodeRef) -> Ty {
        self.get_type_at_location(node)
    }

    fn get_properties_of_type(&self, _t: Ty) -> Vec<SymbolRef> {
        Vec::new()
    }

    fn get_property_of_type(&self, _t: Ty, _name: &str) -> Option<SymbolRef> {
        None
    }

    fn get_signatures_of_type(&self, _t: Ty, _kind: SignatureKind) -> Vec<Signature> {
        Vec::new()
    }

    fn get_index_infos_of_type(&self, _t: Ty) -> Vec<IndexInfo> {
        Vec::new()
    }

    fn is_assignable_to(&self, _source: Ty, _target: Ty) -> bool {
        false
    }

    fn type_to_string(&self, t: Ty, _location: NodeRef) -> String {
        match t {
            Ty::None => "none",
            Ty::Number => "number",
            Ty::String => "string",
            Ty::Boolean => "boolean",
            Ty::Bigint => "bigint",
            Ty::Undefined => "undefined",
            Ty::Null => "null",
            Ty::Any => "any",
            Ty::Unknown => "unknown",
        }
        .to_string()
    }

    fn symbol_to_string(&self, s: SymbolRef, _location: NodeRef) -> String {
        self.semantic(s.program_id)
            .scoping()
            .symbol_name(s.symbol_id)
            .to_string()
    }
}

#[cfg(all(test, any(feature = "conformance", feature = "conformance-tsc")))]
mod conformance;

#[cfg(test)]
mod test {
    use super::*;
    use crate::program::ProgramHost;
    use oxc_allocator::Allocator;
    use oxc_str::Ident;
    use std::cell::RefCell;
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

    fn get_global_symbol_type(ret: &ParseAndCheck, name: &str) -> Ty {
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

    fn get_symbol_type_in_function(ret: &ParseAndCheck, func_name: &str, param_name: &str) -> Ty {
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

        assert_eq!(get_global_symbol_type(&ret, "a"), Ty::Number);
        assert_eq!(get_global_symbol_type(&ret, "b"), Ty::String);
        assert_eq!(get_global_symbol_type(&ret, "c"), Ty::Boolean);
        assert_eq!(get_global_symbol_type(&ret, "d"), Ty::Bigint);
        assert_eq!(get_global_symbol_type(&ret, "e"), Ty::Undefined);
        assert_eq!(get_global_symbol_type(&ret, "f"), Ty::Null);
        assert_eq!(get_global_symbol_type(&ret, "g"), Ty::Any);
        assert_eq!(get_global_symbol_type(&ret, "h"), Ty::Unknown);
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

        assert_eq!(get_global_symbol_type(&ret, "l7"), Ty::Boolean);
        assert_eq!(get_global_symbol_type(&ret, "n"), Ty::Number);
        assert_eq!(get_global_symbol_type(&ret, "s"), Ty::String);
        assert_eq!(get_global_symbol_type(&ret, "b"), Ty::Bigint);
        assert_eq!(get_global_symbol_type(&ret, "a"), Ty::Any);
        assert_eq!(get_global_symbol_type(&ret, "annotated"), Ty::String);
    }

    #[test]
    fn function_parameter_declared_types() {
        let allocator = Allocator::default();
        let ret = parse_and_check_source(
            &allocator,
            "function foo(a: number, b: string, c: boolean) {}",
        );

        assert_eq!(get_symbol_type_in_function(&ret, "foo", "a"), Ty::Number);
        assert_eq!(get_symbol_type_in_function(&ret, "foo", "b"), Ty::String);
        assert_eq!(get_symbol_type_in_function(&ret, "foo", "c"), Ty::Boolean);
    }
}
