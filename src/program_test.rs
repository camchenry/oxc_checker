use super::*;
use crate::checker::{Checker, SymbolRef};
use oxc_str::Ident;
use rustc_hash::FxHashMap;

#[derive(Default)]
struct InMemoryProgramHost {
    cwd: PathBuf,
    files: FxHashMap<PathBuf, String>,
}

impl InMemoryProgramHost {
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

    fn resolve_relative(&self, containing_file: &Path, specifier: &str) -> HostModuleResolution {
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
    let checker = Checker::new(&store);
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
