use std::{cell::RefCell, collections::HashMap};

use oxc_ast::ast::TSInterfaceDeclaration;
use oxc_index::IndexVec;
use oxc_semantic::{NodeId, SymbolId};

use crate::{
    ClassMemberResolution,
    global_types::GlobalSymbolTable,
    program::{ProgramId, ProgramStore},
    types::{CheckerArena, IndexInfo, Signature, SignatureKind, Ty},
};

pub struct CheckerReturn<'a, 'store> {
    pub store: &'store ProgramStore<'a>,
    pub arena: CheckerArena<'a>,
    pub global_symbols: GlobalSymbolTable,
    // TODO(perf): these should use the Arena Vec/HashMap?
    pub declared_type_cache: RefCell<Vec<IndexVec<SymbolId, Option<Ty<'a>>>>>,
    pub interface_declarations_cache:
        RefCell<HashMap<String, &'a [(ProgramId, &'a TSInterfaceDeclaration<'a>)]>>,
    pub resolving_symbols: RefCell<Vec<SymbolRef>>,
    pub resolving_class_members: RefCell<Vec<ClassMemberResolution>>,
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

#[allow(dead_code)]
pub trait Checker<'a> {
    fn get_symbol_at_location(&self, node: NodeRef) -> Option<SymbolRef>;
    fn get_type_at_location(&self, node: NodeRef) -> Ty<'a>;
    // fn get_type_from_type_node(&self, type_node: NodeRef) -> Ty<'a>;
    fn get_declared_type_of_symbol(&self, sym: SymbolRef) -> Ty<'a>;
    fn get_type_of_symbol(&self, sym: SymbolRef) -> Ty<'a>;
    fn get_type_of_symbol_at_location(&self, node: NodeRef) -> Ty<'a>;
    fn get_properties_of_type(&self, t: Ty<'a>) -> Vec<SymbolRef>;
    fn get_property_of_type(&self, t: Ty<'a>, name: &str) -> Option<SymbolRef>;
    fn get_signatures_of_type(&self, t: Ty<'a>, kind: SignatureKind) -> Vec<Signature<'a>>;
    fn get_index_infos_of_type(&self, t: Ty<'a>) -> Vec<IndexInfo<'a>>;
    fn is_assignable_to(&self, source: Ty<'a>, target: Ty<'a>) -> bool;
    fn type_to_string(&self, t: Ty<'a>, location: NodeRef) -> String;
    fn symbol_to_string(&self, s: SymbolRef, location: NodeRef) -> String;
}

pub struct CheckerBuilder {}

impl CheckerBuilder {
    pub fn new() -> Self {
        Self {}
    }

    pub fn build<'a, 'store>(&self, store: &'store ProgramStore<'a>) -> CheckerReturn<'a, 'store> {
        CheckerReturn {
            store,
            arena: CheckerArena::new(store.allocator()),
            global_symbols: GlobalSymbolTable::new(store),
            declared_type_cache: RefCell::new(
                store
                    .entries()
                    .iter()
                    .map(|entry| {
                        IndexVec::from_vec(vec![None; entry.semantic().scoping().symbols_len()])
                    })
                    .collect(),
            ),
            interface_declarations_cache: RefCell::new(HashMap::new()),
            resolving_symbols: RefCell::new(Vec::new()),
            resolving_class_members: RefCell::new(Vec::new()),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NodeRef {
    pub program_id: ProgramId,
    pub node_id: NodeId,
}

impl NodeRef {
    pub fn new(program_id: ProgramId, node_id: NodeId) -> Self {
        Self {
            program_id,
            node_id,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SymbolRef {
    pub program_id: ProgramId,
    pub symbol_id: SymbolId,
}

impl SymbolRef {
    pub fn new(program_id: ProgramId, symbol_id: SymbolId) -> Self {
        Self {
            program_id,
            symbol_id,
        }
    }
}
