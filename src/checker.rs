use std::cell::{Cell, RefCell};

use oxc_ast::ast::{AssignmentExpression, TSInterfaceDeclaration};
use oxc_index::IndexVec;
use oxc_semantic::{NodeId, SymbolId};
use oxc_span::Span;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use crate::{
    flow_graph::ProgramFlowGraph,
    global_types::GlobalSymbolTable,
    mapper::MapperCacheEntry,
    program::{ProgramId, ProgramStore},
    types::{CheckerArena, Ty, TyTypeParameter, TypeBuilder, TypeId},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClassMemberResolution {
    pub(crate) program_id: ProgramId,
    pub(crate) class_name: String,
    pub(crate) property_name: String,
    pub(crate) is_static: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TypeAliasMetadata {
    pub(crate) reference_program_id: ProgramId,
    pub(crate) alias_symbol: SymbolRef,
    pub(crate) declaration: NodeRef,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct TypeAliasResolution {
    pub(crate) program_id: ProgramId,
    pub(crate) declaration: NodeId,
    pub(crate) type_arguments: SmallVec<[TypeId; 4]>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct InstantiationCacheKey<'a> {
    pub(crate) target: TypeId,
    pub(crate) mapper: SmallVec<[MapperCacheEntry<'a>; 1]>,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(crate) struct TypeStringContext {
    pub(crate) in_type_alias: bool,
    pub(crate) expand_transparent_aliases: bool,
    pub(crate) expand_named_alias_chains: bool,
}

impl TypeStringContext {
    pub(crate) fn expands_transparent_aliases(self) -> bool {
        self.in_type_alias || self.expand_transparent_aliases
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct TypeStringCacheKey<'a> {
    pub(crate) ty: Ty<'a>,
    pub(crate) context: TypeStringContext,
}

pub(crate) type SymbolTypeCache<'a> = Vec<Option<IndexVec<SymbolId, Option<Ty<'a>>>>>;

pub struct Checker<'a, 'store> {
    pub(crate) store: &'store ProgramStore<'a>,
    pub(crate) arena: CheckerArena<'a>,
    pub(crate) ty: TypeBuilder<'a>,
    pub(crate) global_symbols: &'store GlobalSymbolTable,
    pub(crate) declared_type_cache: RefCell<SymbolTypeCache<'a>>,
    pub(crate) value_type_cache: RefCell<SymbolTypeCache<'a>>,
    pub(crate) type_alias_metadata_by_type: RefCell<IndexVec<TypeId, Option<TypeAliasMetadata>>>,
    pub(crate) instantiation_cache: RefCell<FxHashMap<InstantiationCacheKey<'a>, Ty<'a>>>,
    pub(crate) type_alias_resolution_cache: RefCell<FxHashMap<TypeAliasResolution, Ty<'a>>>,
    pub(crate) type_parameter_declaration_cache:
        RefCell<FxHashMap<(ProgramId, NodeId), &'a [TyTypeParameter<'a>]>>,
    pub(crate) overflowed_type_alias_resolutions: RefCell<Vec<TypeAliasResolution>>,
    pub(crate) type_string_cache: RefCell<FxHashMap<TypeStringCacheKey<'a>, String>>,
    pub(crate) expando_assignments_by_container:
        RefCell<FxHashMap<ProgramId, FxHashMap<NodeId, Vec<&'a AssignmentExpression<'a>>>>>,
    pub(crate) flow_graph_cache: RefCell<FxHashMap<ProgramId, ProgramFlowGraph>>,
    pub(crate) interface_declarations_cache:
        RefCell<FxHashMap<String, &'a [(ProgramId, &'a TSInterfaceDeclaration<'a>)]>>,
    pub(crate) resolving_symbols: RefCell<Vec<SymbolRef>>,
    pub(crate) resolving_type_aliases: RefCell<Vec<TypeAliasResolution>>,
    pub(crate) resolving_type_parameters: RefCell<Vec<TypeParameterResolution>>,
    pub(crate) resolving_class_members: RefCell<Vec<ClassMemberResolution>>,
    pub(crate) interface_property_resolution_stack: RefCell<Vec<(usize, String, String)>>,
    pub(crate) ts_type_resolution_depth: Cell<usize>,
    pub(crate) hide_implicit_type_argument_display: Cell<bool>,
    pub(crate) type_instantiation_depth: Cell<usize>,
    pub(crate) type_instantiation_count: Cell<usize>,
    pub(crate) type_instantiation_overflowed: Cell<bool>,
    pub(crate) conditional_type_depth: Cell<usize>,
    pub(crate) type_string_depth: Cell<usize>,
}

impl<'a, 'store> Checker<'a, 'store> {
    /// Creates a checker for a program store.
    ///
    /// ```
    /// use oxc_allocator::Allocator;
    /// use oxc_checker::{
    ///     checker::Checker,
    ///     program::{FsProgramHost, ProgramStoreBuilder},
    /// };
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let allocator = Allocator::default();
    /// let store = ProgramStoreBuilder::new(&allocator, FsProgramHost::new())
    ///     .without_default_lib()
    ///     .build()?;
    /// let checker = Checker::new(&store);
    /// assert!(checker.type_count() > 0);
    /// # Ok(())
    /// # }
    /// ```
    pub fn new(store: &'store ProgramStore<'a>) -> Self {
        Self::with_arena(store, CheckerArena::new(store.allocator()))
    }

    pub(crate) fn with_arena(store: &'store ProgramStore<'a>, arena: CheckerArena<'a>) -> Self {
        Self {
            store,
            arena,
            ty: TypeBuilder::new(arena),
            global_symbols: store.global_symbols(),
            declared_type_cache: RefCell::new(store.entries().iter().map(|_| None).collect()),
            value_type_cache: RefCell::new(store.entries().iter().map(|_| None).collect()),
            type_alias_metadata_by_type: RefCell::new(IndexVec::from_vec(vec![
                None;
                arena.type_count()
            ])),
            instantiation_cache: RefCell::new(FxHashMap::default()),
            type_alias_resolution_cache: RefCell::new(FxHashMap::default()),
            type_parameter_declaration_cache: RefCell::new(FxHashMap::default()),
            overflowed_type_alias_resolutions: RefCell::new(Vec::new()),
            type_string_cache: RefCell::new(FxHashMap::default()),
            expando_assignments_by_container: RefCell::new(FxHashMap::default()),
            flow_graph_cache: RefCell::new(FxHashMap::default()),
            interface_declarations_cache: RefCell::new(FxHashMap::default()),
            resolving_symbols: RefCell::new(Vec::new()),
            resolving_type_aliases: RefCell::new(Vec::new()),
            resolving_type_parameters: RefCell::new(Vec::new()),
            resolving_class_members: RefCell::new(Vec::new()),
            interface_property_resolution_stack: RefCell::new(Vec::new()),
            ts_type_resolution_depth: Cell::new(0),
            hide_implicit_type_argument_display: Cell::new(false),
            type_instantiation_depth: Cell::new(0),
            type_instantiation_count: Cell::new(0),
            type_instantiation_overflowed: Cell::new(false),
            conditional_type_depth: Cell::new(0),
            type_string_depth: Cell::new(0),
        }
    }
}

impl<'a> Checker<'a, '_> {
    pub fn type_count(&self) -> usize {
        self.arena.type_count()
    }

    pub(crate) fn cached_symbol_type(
        &self,
        cache: &RefCell<SymbolTypeCache<'a>>,
        symbol: SymbolRef,
    ) -> Option<Ty<'a>> {
        cache
            .borrow()
            .get(symbol.program_id.index())
            .and_then(Option::as_ref)
            .and_then(|cache| cache.get(symbol.symbol_id))
            .copied()
            .flatten()
    }

    pub(crate) fn cache_symbol_type(
        &self,
        cache: &RefCell<SymbolTypeCache<'a>>,
        symbol: SymbolRef,
        ty: Ty<'a>,
    ) {
        let mut cache = cache.borrow_mut();
        let Some(program_cache) = cache.get_mut(symbol.program_id.index()) else {
            return;
        };
        let program_cache = program_cache.get_or_insert_with(|| {
            IndexVec::from_vec(vec![
                None;
                self.semantic(symbol.program_id).scoping().symbols_len()
            ])
        });
        if let Some(slot) = program_cache.get_mut(symbol.symbol_id) {
            *slot = Some(ty);
        }
    }

    pub fn types(&self) -> impl ExactSizeIterator<Item = Ty<'a>> {
        self.arena.types()
    }

    pub fn type_ids(&self) -> impl ExactSizeIterator<Item = TypeId> {
        self.arena.type_ids()
    }

    pub fn type_from_id(&self, id: TypeId) -> Option<Ty<'a>> {
        self.arena.type_from_id(id)
    }

    pub fn is_type_identical_to(&self, left: Ty<'a>, right: Ty<'a>) -> bool {
        self.arena.is_type_identical_to(left, right)
    }

    pub(crate) fn set_type_alias_metadata(&self, ty: Ty<'a>, metadata: TypeAliasMetadata) {
        let mut metadata_by_type = self.type_alias_metadata_by_type.borrow_mut();
        metadata_by_type.resize(self.arena.type_count(), None);
        metadata_by_type[ty.id()] = Some(metadata);
        self.type_string_cache.borrow_mut().clear();
    }

    pub(crate) fn type_alias_metadata(&self, ty: Ty<'a>) -> Option<TypeAliasMetadata> {
        self.type_alias_metadata_by_type
            .borrow()
            .get(ty.id())
            .copied()
            .flatten()
    }

    pub(crate) fn copy_type_alias_metadata(&self, source: Ty<'a>, target: Ty<'a>) {
        if let Some(metadata) = self.type_alias_metadata(source) {
            self.set_type_alias_metadata(target, metadata);
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeParameterResolution {
    Symbol(SymbolRef),
    Span(ProgramId, Span),
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
