use std::{
    collections::HashMap,
    fmt,
    path::{Component, Path, PathBuf},
};

use oxc_allocator::Allocator;
use oxc_ast::{
    AstKind,
    ast::{Expression, Program},
};
use oxc_index::{Idx, IndexVec};
use oxc_parser::Parser;
use oxc_resolver::{ResolveError, ResolveOptions, Resolver};
use oxc_semantic::{Semantic, SemanticBuilder};
use oxc_span::{SourceType, Span};
use oxc_syntax::module_record::ModuleRecord;

use crate::global_types::GlobalSymbolTable;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProgramId(usize);

impl ProgramId {
    #[inline]
    pub const fn index(self) -> usize {
        self.0
    }
}

impl Idx for ProgramId {
    const MAX: usize = usize::MAX;

    unsafe fn from_usize_unchecked(index: usize) -> Self {
        Self(index)
    }

    fn index(self) -> usize {
        Self::index(self)
    }
}

pub struct ProgramEntry<'a> {
    id: ProgramId,
    path: PathBuf,
    data: ProgramEntryData<'a>,
    /// Whether this entry is a default standard library file injected by the
    /// checker rather than user source. Consumers (e.g. conformance record
    /// extraction) skip lib entries.
    is_lib: bool,
}

impl<'a> ProgramEntry<'a> {
    #[inline]
    pub const fn id(&self) -> ProgramId {
        self.id
    }

    #[inline]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[inline]
    pub const fn source_text(&self) -> &'a str {
        self.data.program().source_text
    }

    #[inline]
    pub const fn source_type(&self) -> SourceType {
        self.data.program().source_type
    }

    #[inline]
    pub const fn program(&self) -> &'a Program<'a> {
        self.data.program().program
    }

    #[inline]
    pub const fn module_record(&self) -> &ModuleRecord<'a> {
        &self.data.program().module_record
    }

    #[inline]
    pub const fn semantic(&self) -> &Semantic<'a> {
        &self.data.program().semantic
    }

    #[inline]
    pub const fn is_lib(&self) -> bool {
        self.is_lib
    }
}

enum ProgramEntryData<'a> {
    Owned(Box<PreparedProgram<'a>>),
    Prepared(&'a PreparedProgram<'a>),
}

impl<'a> ProgramEntryData<'a> {
    const fn program(&self) -> &PreparedProgram<'a> {
        match self {
            Self::Owned(program) => program,
            Self::Prepared(program) => program,
        }
    }
}

/// Immutable parser and semantic output that can be reused by multiple program stores.
struct PreparedProgram<'a> {
    source_text: &'a str,
    source_type: SourceType,
    program: &'a Program<'a>,
    module_record: ModuleRecord<'a>,
    semantic: Semantic<'a>,
}

/// A path-indexed collection of immutable programs parsed in one allocator.
pub struct PreparedProgramSet<'a> {
    allocator: &'a Allocator,
    programs: HashMap<PathBuf, PreparedProgram<'a>>,
}

impl<'a> PreparedProgramSet<'a> {
    #[must_use]
    pub fn new(allocator: &'a Allocator) -> Self {
        Self {
            allocator,
            programs: HashMap::new(),
        }
    }

    pub fn add_source(
        &mut self,
        path: impl Into<PathBuf>,
        source_text: &str,
        source_type: SourceType,
    ) -> ProgramStoreResult<()> {
        let path = path.into();
        let source_text = self.allocator.alloc_str(source_text);
        let program = parse_program(self.allocator, &path, source_text, source_type)?;
        self.programs.insert(path, program);
        Ok(())
    }

    /// Parse every embedded standard-library program so stores can cheaply select any target.
    pub fn embedded_libraries(allocator: &'a Allocator) -> ProgramStoreResult<Self> {
        let mut programs = Self::new(allocator);
        for file in crate::global_lib::all_lib_files() {
            programs.add_source(file.virtual_path, file.contents, SourceType::d_ts())?;
        }
        Ok(programs)
    }

    fn get(&self, path: &Path) -> Option<&PreparedProgram<'a>> {
        self.programs.get(path)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleEdge {
    from: ProgramId,
    specifier: String,
    span: Span,
    is_type: bool,
    is_import: bool,
    resolution: ModuleEdgeResolution,
}

impl ModuleEdge {
    #[inline]
    pub const fn from(&self) -> ProgramId {
        self.from
    }

    #[inline]
    pub fn specifier(&self) -> &str {
        &self.specifier
    }

    #[inline]
    pub const fn span(&self) -> Span {
        self.span
    }

    #[inline]
    pub const fn is_type(&self) -> bool {
        self.is_type
    }

    #[inline]
    pub const fn is_import(&self) -> bool {
        self.is_import
    }

    #[inline]
    pub const fn resolution(&self) -> &ModuleEdgeResolution {
        &self.resolution
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModuleEdgeResolution {
    Resolved(ProgramId),
    Missing(String),
    External(String),
    Builtin(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostModuleResolution {
    Path(PathBuf),
    Missing(String),
    External(String),
    Builtin(String),
}

pub trait ProgramHost {
    fn read_source(&self, path: &Path) -> ProgramStoreResult<String>;

    fn canonicalize_path(&self, path: &Path) -> PathBuf {
        normalize_path(path)
    }

    fn resolve_module(&self, containing_file: &Path, specifier: &str) -> HostModuleResolution;
}

pub struct FsProgramHost {
    resolver: Resolver,
}

impl FsProgramHost {
    #[must_use]
    pub fn new() -> Self {
        Self::with_options(ts_resolve_options())
    }

    #[must_use]
    pub fn with_options(options: ResolveOptions) -> Self {
        Self {
            resolver: Resolver::new(options),
        }
    }
}

impl Default for FsProgramHost {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgramHost for FsProgramHost {
    fn read_source(&self, path: &Path) -> ProgramStoreResult<String> {
        std::fs::read_to_string(path).map_err(|error| ProgramStoreError::ReadSource {
            path: path.to_path_buf(),
            message: error.to_string(),
        })
    }

    fn canonicalize_path(&self, path: &Path) -> PathBuf {
        std::fs::canonicalize(path).unwrap_or_else(|_| normalize_path(path))
    }

    fn resolve_module(&self, containing_file: &Path, specifier: &str) -> HostModuleResolution {
        match self.resolver.resolve_file(containing_file, specifier) {
            Ok(resolution) => HostModuleResolution::Path(self.canonicalize_path(resolution.path())),
            Err(ResolveError::Builtin { resolved, .. }) => HostModuleResolution::Builtin(resolved),
            Err(ResolveError::NotFound(_)) => HostModuleResolution::Missing(specifier.to_string()),
            Err(error) => HostModuleResolution::Missing(error.to_string()),
        }
    }
}

pub struct ProgramStoreBuilder<'a, H> {
    allocator: &'a Allocator,
    host: H,
    root_files: Vec<PathBuf>,
    load_default_lib: bool,
    lib_selection: crate::global_lib::LibSelection,
    prepared_programs: Option<&'a PreparedProgramSet<'a>>,
}

impl<'a, H: ProgramHost> ProgramStoreBuilder<'a, H> {
    pub fn new(allocator: &'a Allocator, host: H) -> Self {
        Self {
            allocator,
            host,
            root_files: Vec::new(),
            load_default_lib: true,
            lib_selection: crate::global_lib::LibSelection::default(),
            prepared_programs: None,
        }
    }

    /// Reuse immutable parser and semantic output for matching canonical paths.
    pub fn with_prepared_programs(mut self, programs: &'a PreparedProgramSet<'a>) -> Self {
        self.prepared_programs = Some(programs);
        self
    }

    pub fn add_root_file(mut self, path: impl Into<PathBuf>) -> Self {
        self.root_files.push(path.into());
        self
    }

    pub fn with_default_lib_target_name(mut self, target: &str) -> ProgramStoreResult<Self> {
        let Some(target) = crate::global_lib::LibTarget::parse(target) else {
            return Err(ProgramStoreError::LibSelection {
                message: format!("unsupported target `{}`", target.trim()),
            });
        };
        self.lib_selection = crate::global_lib::LibSelection::DefaultTarget(target);
        Ok(self)
    }

    pub fn with_lib_names<I, S>(mut self, lib_names: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.lib_selection = crate::global_lib::LibSelection::Explicit(
            lib_names.into_iter().map(Into::into).collect(),
        );
        self
    }

    /// Disable injecting embedded default standard library files.
    pub fn without_default_lib(mut self) -> Self {
        self.load_default_lib = false;
        self
    }

    pub fn build(self) -> ProgramStoreResult<ProgramStore<'a>> {
        let mut store = ProgramStore::new(self.allocator);
        // Inject the default standard library before user files so global
        // ambient declarations (Array, Promise, ...) are available to every
        // program in the store.
        if self.load_default_lib {
            self.inject_default_libs(&mut store)?;
        }
        for root_file in &self.root_files {
            let root_file = self.host.canonicalize_path(root_file);
            self.ensure_program(&mut store, &root_file)?;
        }
        store.global_symbols = GlobalSymbolTable::new(&store);
        Ok(store)
    }

    /// Parse and store the embedded default standard library files as ambient
    /// lib entries.
    ///
    /// TODO(perf): these files are reparsed for every `ProgramStore`. Consider
    /// sharing or caching parsed lib programs across builds.
    fn inject_default_libs(&self, store: &mut ProgramStore<'a>) -> ProgramStoreResult<()> {
        let lib_files = crate::global_lib::resolve_lib_files(&self.lib_selection)
            .map_err(|message| ProgramStoreError::LibSelection { message })?;
        for lib_file in lib_files {
            let path = PathBuf::from(lib_file.virtual_path);
            if let Some(program) = self
                .prepared_programs
                .and_then(|programs| programs.get(&path))
            {
                self.build_entry_from_prepared(store, path, program, true)?;
                continue;
            }
            let source_text = self.allocator.alloc_str(lib_file.contents);
            self.build_entry_from_source(store, path, source_text, SourceType::d_ts(), true)?;
        }
        Ok(())
    }

    fn ensure_program(
        &self,
        store: &mut ProgramStore<'a>,
        path: &Path,
    ) -> ProgramStoreResult<ProgramId> {
        let path = self.host.canonicalize_path(path);
        if let Some(id) = store.id_for_path(&path) {
            return Ok(id);
        }

        if let Some(program) = self
            .prepared_programs
            .and_then(|programs| programs.get(&path))
        {
            return self.build_entry_from_prepared(store, path, program, false);
        }

        let source_text = self.host.read_source(&path)?;
        let source_text = self.allocator.alloc_str(&source_text);
        let source_type = SourceType::from_path(&path).unwrap_or_else(|_| SourceType::ts());
        self.build_entry_from_source(store, path, source_text, source_type, false)
    }

    /// Parse `source_text`, run semantic analysis, store the resulting entry,
    /// and process its module edges. Shared by user-file loading
    /// (`ensure_program`) and default lib injection (`inject_default_libs`).
    fn build_entry_from_source(
        &self,
        store: &mut ProgramStore<'a>,
        path: PathBuf,
        source_text: &'a str,
        source_type: SourceType,
        is_lib: bool,
    ) -> ProgramStoreResult<ProgramId> {
        let program = parse_program(self.allocator, &path, source_text, source_type)?;
        self.build_entry(
            store,
            path,
            ProgramEntryData::Owned(Box::new(program)),
            is_lib,
        )
    }

    fn build_entry_from_prepared(
        &self,
        store: &mut ProgramStore<'a>,
        path: PathBuf,
        program: &'a PreparedProgram<'a>,
        is_lib: bool,
    ) -> ProgramStoreResult<ProgramId> {
        self.build_entry(store, path, ProgramEntryData::Prepared(program), is_lib)
    }

    fn build_entry(
        &self,
        store: &mut ProgramStore<'a>,
        path: PathBuf,
        data: ProgramEntryData<'a>,
        is_lib: bool,
    ) -> ProgramStoreResult<ProgramId> {
        let id = store.push_entry(|id| ProgramEntry {
            id,
            path: path.clone(),
            data,
            is_lib,
        });

        let requests = store.module_requests(id);
        for request in requests {
            let resolution = match self.host.resolve_module(&path, &request.specifier) {
                HostModuleResolution::Path(resolved_path) => {
                    let resolved_path = self.host.canonicalize_path(&resolved_path);
                    ModuleEdgeResolution::Resolved(self.ensure_program(store, &resolved_path)?)
                }
                HostModuleResolution::Missing(message) => ModuleEdgeResolution::Missing(message),
                HostModuleResolution::External(specifier) => {
                    ModuleEdgeResolution::External(specifier)
                }
                HostModuleResolution::Builtin(specifier) => {
                    ModuleEdgeResolution::Builtin(specifier)
                }
            };
            store.edges.push(ModuleEdge {
                from: id,
                specifier: request.specifier,
                span: request.span,
                is_type: request.is_type,
                is_import: request.is_import,
                resolution,
            });
        }

        Ok(id)
    }
}

fn parse_program<'a>(
    allocator: &'a Allocator,
    path: &Path,
    source_text: &'a str,
    source_type: SourceType,
) -> ProgramStoreResult<PreparedProgram<'a>> {
    let parser_return = Parser::new(allocator, source_text, source_type).parse();
    if parser_return.panicked {
        return Err(ProgramStoreError::Parse {
            path: path.to_path_buf(),
            messages: parser_return
                .diagnostics
                .iter()
                .map(ToString::to_string)
                .collect(),
        });
    }

    let program = allocator.alloc(parser_return.program);
    let semantic_return = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .build(program);
    // Keep building even when semantic analysis reports recoverable errors so downstream
    // consumers can still inspect partial symbol and type data.
    Ok(PreparedProgram {
        source_text,
        source_type,
        program,
        module_record: parser_return.module_record,
        semantic: semantic_return.semantic,
    })
}

pub struct ProgramStore<'a> {
    allocator: &'a Allocator,
    entries: IndexVec<ProgramId, ProgramEntry<'a>>,
    paths: HashMap<PathBuf, ProgramId>,
    edges: Vec<ModuleEdge>,
    global_symbols: GlobalSymbolTable,
}

impl<'a> ProgramStore<'a> {
    #[must_use]
    pub fn new(allocator: &'a Allocator) -> Self {
        Self {
            allocator,
            entries: IndexVec::new(),
            paths: HashMap::new(),
            edges: Vec::new(),
            global_symbols: GlobalSymbolTable::default(),
        }
    }

    #[inline]
    pub const fn allocator(&self) -> &'a Allocator {
        self.allocator
    }

    #[inline]
    pub fn entries(&self) -> &[ProgramEntry<'a>] {
        &self.entries.raw
    }

    #[inline]
    pub fn edges(&self) -> &[ModuleEdge] {
        &self.edges
    }

    #[inline]
    pub fn entry(&self, id: ProgramId) -> Option<&ProgramEntry<'a>> {
        self.entries.get(id)
    }

    #[inline]
    pub fn id_for_path(&self, path: &Path) -> Option<ProgramId> {
        self.paths.get(path).copied()
    }

    pub fn entry_for_path(&self, path: &Path) -> Option<&ProgramEntry<'a>> {
        self.id_for_path(path).and_then(|id| self.entry(id))
    }

    #[inline]
    pub(crate) const fn global_symbols(&self) -> &GlobalSymbolTable {
        &self.global_symbols
    }

    pub fn module_edges(&self, id: ProgramId) -> impl Iterator<Item = &ModuleEdge> {
        self.edges.iter().filter(move |edge| edge.from == id)
    }

    pub fn resolved_module(&self, from: ProgramId, specifier: &str) -> Option<ProgramId> {
        self.module_edges(from).find_map(|edge| {
            if edge.specifier == specifier {
                match edge.resolution {
                    ModuleEdgeResolution::Resolved(id) => Some(id),
                    _ => None,
                }
            } else {
                None
            }
        })
    }

    fn push_entry(&mut self, create_entry: impl FnOnce(ProgramId) -> ProgramEntry<'a>) -> ProgramId {
        let id = self.entries.next_idx();
        let entry = create_entry(id);
        let id = entry.id;
        self.paths.insert(entry.path.clone(), id);
        self.entries.push(entry);
        id
    }

    fn module_requests(&self, id: ProgramId) -> Vec<PendingModuleRequest> {
        let mut requests = Vec::new();
        let Some(entry) = self.entry(id) else {
            return requests;
        };
        for (specifier, occurrences) in &entry.module_record().requested_modules {
            for occurrence in occurrences {
                requests.push(PendingModuleRequest {
                    specifier: specifier.as_str().to_string(),
                    span: occurrence.span,
                    is_type: occurrence.is_type,
                    is_import: occurrence.is_import,
                });
            }
        }
        for node in entry.semantic().nodes().iter() {
            match node.kind() {
                AstKind::ImportExpression(import_expression) => {
                    let Expression::StringLiteral(source) = &import_expression.source else {
                        continue;
                    };
                    requests.push(PendingModuleRequest {
                        specifier: source.value.as_str().to_string(),
                        span: import_expression.span,
                        is_type: false,
                        is_import: true,
                    });
                }
                AstKind::TSImportType(import_type) => {
                    requests.push(PendingModuleRequest {
                        specifier: import_type.source.value.as_str().to_string(),
                        span: import_type.span,
                        is_type: true,
                        is_import: true,
                    });
                }
                _ => {}
            }
        }
        requests
    }
}

impl<'a> std::ops::Index<ProgramId> for ProgramStore<'a> {
    type Output = ProgramEntry<'a>;

    fn index(&self, id: ProgramId) -> &Self::Output {
        &self.entries[id]
    }
}

struct PendingModuleRequest {
    specifier: String,
    span: Span,
    is_type: bool,
    is_import: bool,
}

pub type ProgramStoreResult<T> = Result<T, ProgramStoreError>;

#[derive(Debug)]
pub enum ProgramStoreError {
    LibSelection {
        message: String,
    },
    ReadSource {
        path: PathBuf,
        message: String,
    },
    Parse {
        path: PathBuf,
        messages: Vec<String>,
    },
    Semantic {
        path: PathBuf,
        messages: Vec<String>,
    },
}

impl fmt::Display for ProgramStoreError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LibSelection { message } => {
                write!(
                    formatter,
                    "failed to select standard library files: {message}"
                )
            }
            Self::ReadSource { path, message } => {
                write!(formatter, "failed to read {}: {message}", path.display())
            }
            Self::Parse { path, messages } => {
                write!(
                    formatter,
                    "parse errors in {}: {}",
                    path.display(),
                    messages.join("; ")
                )
            }
            Self::Semantic { path, messages } => {
                write!(
                    formatter,
                    "semantic errors in {}: {}",
                    path.display(),
                    messages.join("; ")
                )
            }
        }
    }
}

impl std::error::Error for ProgramStoreError {}

#[must_use]
pub fn ts_resolve_options() -> ResolveOptions {
    ResolveOptions {
        extensions: vec![
            ".ts".to_string(),
            ".tsx".to_string(),
            ".d.ts".to_string(),
            ".js".to_string(),
            ".jsx".to_string(),
            ".json".to_string(),
            ".node".to_string(),
        ],
        extension_alias: vec![
            (
                ".js".to_string(),
                vec![
                    ".ts".to_string(),
                    ".tsx".to_string(),
                    ".d.ts".to_string(),
                    ".js".to_string(),
                ],
            ),
            (
                ".jsx".to_string(),
                vec![".tsx".to_string(), ".jsx".to_string()],
            ),
            (
                ".mjs".to_string(),
                vec![".mts".to_string(), ".mjs".to_string()],
            ),
            (
                ".cjs".to_string(),
                vec![".cts".to_string(), ".cjs".to_string()],
            ),
        ],
        builtin_modules: true,
        ..ResolveOptions::default()
    }
}

fn normalize_path(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                normalized.pop();
            }
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(component.as_os_str()),
            Component::Normal(part) => normalized.push(part),
        }
    }
    normalized
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker::{Checker, CheckerBuilder, SymbolRef};
    use oxc_str::Ident;

    #[derive(Default)]
    struct InMemoryProgramHost {
        cwd: PathBuf,
        files: HashMap<PathBuf, String>,
    }

    impl InMemoryProgramHost {
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

        fn resolve_relative(
            &self,
            containing_file: &Path,
            specifier: &str,
        ) -> HostModuleResolution {
            if !(specifier.starts_with('.') || specifier.starts_with('/')) {
                return HostModuleResolution::External(specifier.to_string());
            }

            let containing_dir = containing_file.parent().unwrap_or_else(|| Path::new(""));
            let base = self.canonicalize_path(&containing_dir.join(specifier));
            if self.files.contains_key(&base) {
                return HostModuleResolution::Path(base);
            }

            for extension in ["ts", "tsx", "d.ts", "js", "jsx", "json"] {
                let mut candidate = base.clone();
                candidate.set_extension(extension);
                if self.files.contains_key(&candidate) {
                    return HostModuleResolution::Path(candidate);
                }
            }

            for extension in ["ts", "tsx", "d.ts", "js", "jsx", "json"] {
                let candidate = base.join(format!("index.{extension}"));
                if self.files.contains_key(&candidate) {
                    return HostModuleResolution::Path(candidate);
                }
            }

            HostModuleResolution::Missing(specifier.to_string())
        }
    }

    impl ProgramHost for InMemoryProgramHost {
        fn read_source(&self, path: &Path) -> ProgramStoreResult<String> {
            self.files
                .get(&self.canonicalize_path(path))
                .cloned()
                .ok_or_else(|| ProgramStoreError::ReadSource {
                    path: path.to_path_buf(),
                    message: "file not found".to_string(),
                })
        }

        fn canonicalize_path(&self, path: &Path) -> PathBuf {
            if path.is_absolute() {
                normalize_path(path)
            } else {
                normalize_path(&self.cwd.join(path))
            }
        }

        fn resolve_module(&self, containing_file: &Path, specifier: &str) -> HostModuleResolution {
            self.resolve_relative(containing_file, specifier)
        }
    }

    #[test]
    fn builds_single_root_program() {
        let allocator = Allocator::default();
        let host = InMemoryProgramHost::new("/project")
            .add_file("/project/a.ts", "export const a: number = 1;");

        let store = ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/a.ts")
            .without_default_lib()
            .build()
            .unwrap();

        assert_eq!(store.entries().len(), 1);
        assert!(store.edges().is_empty());
        assert_eq!(store.entries()[0].path(), Path::new("/project/a.ts"));
    }

    #[test]
    fn prepared_programs_are_reused_with_store_local_ids() {
        let allocator = Allocator::default();
        let mut prepared = PreparedProgramSet::new(&allocator);
        prepared
            .add_source(
                "/shared/types.d.ts",
                "interface Shared { value: string }",
                SourceType::d_ts(),
            )
            .unwrap();

        let first = ProgramStoreBuilder::new(
            &allocator,
            InMemoryProgramHost::new("/first")
                .add_file("/first/main.ts", "declare const value: Shared;"),
        )
        .with_prepared_programs(&prepared)
        .add_root_file("/shared/types.d.ts")
        .add_root_file("/first/main.ts")
        .without_default_lib()
        .build()
        .unwrap();
        let second = ProgramStoreBuilder::new(
            &allocator,
            InMemoryProgramHost::new("/second")
                .add_file("/second/main.ts", "declare const value: Shared;"),
        )
        .with_prepared_programs(&prepared)
        .add_root_file("/shared/types.d.ts")
        .add_root_file("/second/main.ts")
        .without_default_lib()
        .build()
        .unwrap();

        let first_id = first.id_for_path(Path::new("/shared/types.d.ts")).unwrap();
        let second_id = second.id_for_path(Path::new("/shared/types.d.ts")).unwrap();
        let first_entry = first.entry(first_id).unwrap();
        let second_entry = second.entry(second_id).unwrap();

        assert_eq!(first_id, ProgramId(0));
        assert_eq!(second_id, ProgramId(0));
        assert!(std::ptr::eq(first_entry.program(), second_entry.program()));
        assert!(std::ptr::eq(
            first_entry.semantic(),
            second_entry.semantic()
        ));
    }

    #[test]
    fn prepared_embedded_libraries_respect_each_store_selection() {
        let allocator = Allocator::default();
        let prepared = PreparedProgramSet::embedded_libraries(&allocator).unwrap();
        let first = ProgramStoreBuilder::new(
            &allocator,
            InMemoryProgramHost::new("/first")
                .add_file("/first/main.ts", "const value: Promise<string> = null!;"),
        )
        .with_prepared_programs(&prepared)
        .with_default_lib_target_name("es5")
        .unwrap()
        .add_root_file("/first/main.ts")
        .build()
        .unwrap();
        let second = ProgramStoreBuilder::new(
            &allocator,
            InMemoryProgramHost::new("/second")
                .add_file("/second/main.ts", "const value: Promise<string> = null!;"),
        )
        .with_prepared_programs(&prepared)
        .with_default_lib_target_name("es2015")
        .unwrap()
        .add_root_file("/second/main.ts")
        .build()
        .unwrap();

        let first_es5 = first.entry_for_path(Path::new("lib.es5.d.ts")).unwrap();
        let second_es5 = second.entry_for_path(Path::new("lib.es5.d.ts")).unwrap();

        assert!(std::ptr::eq(first_es5.program(), second_es5.program()));
        assert!(
            first
                .entry_for_path(Path::new("lib.es2015.promise.d.ts"))
                .is_none()
        );
        assert!(
            second
                .entry_for_path(Path::new("lib.es2015.promise.d.ts"))
                .is_some()
        );
    }

    #[test]
    fn follows_static_imports() {
        let allocator = Allocator::default();
        let host = InMemoryProgramHost::new("/project")
            .add_file(
                "/project/a.ts",
                "import { b } from './b'; export const a: number = b;",
            )
            .add_file("/project/b.ts", "export const b: number = 1;");

        let store = ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/a.ts")
            .without_default_lib()
            .build()
            .unwrap();

        let a = store.id_for_path(Path::new("/project/a.ts")).unwrap();
        let b = store.id_for_path(Path::new("/project/b.ts")).unwrap();

        assert_eq!(store.entries().len(), 2);
        assert_eq!(store.resolved_module(a, "./b"), Some(b));
    }

    #[test]
    fn records_missing_imports_without_loading_a_file() {
        let allocator = Allocator::default();
        let host = InMemoryProgramHost::new("/project")
            .add_file("/project/a.ts", "import { b } from './missing'; b;");

        let store = ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/a.ts")
            .without_default_lib()
            .build()
            .unwrap();

        let edge = store.edges().first().unwrap();
        assert_eq!(store.entries().len(), 1);
        assert_eq!(edge.specifier(), "./missing");
        assert_eq!(
            edge.resolution(),
            &ModuleEdgeResolution::Missing("./missing".to_string())
        );
    }

    #[test]
    fn treats_bare_specifiers_as_external() {
        let allocator = Allocator::default();
        let host = InMemoryProgramHost::new("/project")
            .add_file("/project/a.ts", "import value from 'pkg'; value;");

        let store = ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/a.ts")
            .without_default_lib()
            .build()
            .unwrap();

        assert_eq!(store.entries().len(), 1);
        assert_eq!(
            store.edges().first().unwrap().resolution(),
            &ModuleEdgeResolution::External("pkg".to_string())
        );
    }

    #[test]
    fn infers_type_from_imported_variable_initializer() {
        let allocator = Allocator::default();
        let host = InMemoryProgramHost::new("/project")
            .add_file(
                "/project/a.ts",
                "import { value } from './b'; const result = value;",
            )
            .add_file("/project/b.ts", "export const value = 'hello';");

        let store = ProgramStoreBuilder::new(&allocator, host)
            .add_root_file("/project/a.ts")
            .build()
            .unwrap();
        let program_id = store.id_for_path(Path::new("/project/a.ts")).unwrap();
        let checker = CheckerBuilder::new().build(&store);
        let symbol_id = store
            .entry(program_id)
            .unwrap()
            .semantic()
            .scoping()
            .get_root_binding(Ident::from("result"))
            .unwrap();
        let symbol = SymbolRef::new(program_id, symbol_id);

        assert_eq!(checker.get_type_of_symbol(symbol), crate::Ty::string());
    }
}
