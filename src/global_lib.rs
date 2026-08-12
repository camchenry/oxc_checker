//! Embedded TypeScript standard library (`.d.ts`) declarations.
//!
//! The files under `src/lib/` are copied verbatim from the TypeScript compiler.
//! They are embedded into the binary so the checker can load global library
//! declarations without touching the file system.
//!
//! TypeScript and TypeScript-Go map a `target` to an aggregate library file such
//! as `lib.es2022.full.d.ts`, then let the program loader follow the referenced
//! concrete library files. We embed and load those concrete files directly, so
//! target selection expands to the ordered concrete file list below.

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum LibTarget {
    Es5,
    Es2015,
    Es2016,
    Es2017,
    Es2018,
    Es2019,
    Es2020,
    Es2021,
    Es2022,
    EsNext,
}

impl LibTarget {
    pub(crate) fn parse(value: &str) -> Option<Self> {
        let value = value
            .split(',')
            .next()
            .unwrap_or(value)
            .trim()
            .to_ascii_lowercase();
        match value.as_str() {
            "es3" | "es5" => Some(Self::Es5),
            "es6" | "es2015" => Some(Self::Es2015),
            "es7" | "es2016" => Some(Self::Es2016),
            "es2017" => Some(Self::Es2017),
            "es2018" => Some(Self::Es2018),
            "es2019" => Some(Self::Es2019),
            "es2020" => Some(Self::Es2020),
            "es2021" => Some(Self::Es2021),
            "es2022" => Some(Self::Es2022),
            // TODO(correctness): embed ES2023+ libs instead of capping newer
            // yearly targets at the highest bundled yearly target.
            "es2023" | "es2024" | "es2025" => Some(Self::Es2022),
            "esnext" | "latest" => Some(Self::EsNext),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum LibSelection {
    DefaultTarget(LibTarget),
    Explicit(Vec<String>),
}

impl Default for LibSelection {
    fn default() -> Self {
        Self::DefaultTarget(DEFAULT_LIB_TARGET)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct EmbeddedLibFile {
    pub(crate) virtual_path: &'static str,
    pub(crate) contents: &'static str,
}

#[derive(Clone, Copy)]
struct LibCatalogEntry {
    file: EmbeddedLibFile,
    es_target: Option<LibTarget>,
    default_host: bool,
}

pub(crate) const DEFAULT_LIB_TARGET: LibTarget = LibTarget::Es2020;

#[cfg(test)]
#[expect(clippy::expect_used)]
pub(crate) fn default_lib_files() -> Vec<EmbeddedLibFile> {
    resolve_lib_files(&LibSelection::default()).expect("default lib selection should be valid")
}

pub(crate) fn resolve_lib_files(selection: &LibSelection) -> Result<Vec<EmbeddedLibFile>, String> {
    let mut files = Vec::new();
    match selection {
        LibSelection::DefaultTarget(target) => {
            append_target_files(&mut files, *target);
            append_default_host_files(&mut files);
        }
        LibSelection::Explicit(names) => {
            for name in names {
                append_lib_name(&mut files, name)?;
            }
            sort_by_catalog_order(&mut files);
        }
    }
    Ok(files)
}

pub(crate) fn all_lib_files() -> impl Iterator<Item = EmbeddedLibFile> {
    LIB_CATALOG.iter().map(|entry| entry.file)
}

fn append_target_files(files: &mut Vec<EmbeddedLibFile>, target: LibTarget) {
    for entry in LIB_CATALOG {
        if entry
            .es_target
            .is_some_and(|entry_target| entry_target <= target)
        {
            push_unique(files, entry.file);
        }
    }
}

fn append_default_host_files(files: &mut Vec<EmbeddedLibFile>) {
    for entry in LIB_CATALOG {
        if entry.default_host {
            push_unique(files, entry.file);
        }
    }
}

fn append_lib_name(files: &mut Vec<EmbeddedLibFile>, name: &str) -> Result<(), String> {
    let normalized = normalize_lib_name(name);
    if let Some(target) = aggregate_lib_target(&normalized) {
        append_target_files(files, target);
        return Ok(());
    }

    let Some(virtual_path) = lib_name_to_virtual_path(&normalized) else {
        return Err(format!("unsupported lib `{}`", name.trim()));
    };
    let Some(file) = file_by_virtual_path(virtual_path) else {
        return Err(format!(
            "embedded lib file `{virtual_path}` is not available"
        ));
    };
    push_unique(files, file);
    Ok(())
}

fn normalize_lib_name(name: &str) -> String {
    let mut name = name.trim().to_ascii_lowercase();
    if let Some(stripped) = name.strip_prefix("lib.") {
        name = stripped.to_string();
    }
    if let Some(stripped) = name.strip_suffix(".d.ts") {
        name = stripped.to_string();
    }
    name
}

fn aggregate_lib_target(name: &str) -> Option<LibTarget> {
    match name {
        "es5" => Some(LibTarget::Es5),
        "es6" | "es2015" => Some(LibTarget::Es2015),
        "es7" | "es2016" => Some(LibTarget::Es2016),
        "es2017" => Some(LibTarget::Es2017),
        "es2018" => Some(LibTarget::Es2018),
        "es2019" => Some(LibTarget::Es2019),
        "es2020" => Some(LibTarget::Es2020),
        "es2021" => Some(LibTarget::Es2021),
        "es2022" => Some(LibTarget::Es2022),
        // TODO(correctness): embed ES2023+ libs instead of capping newer
        // yearly aggregate libs at the highest bundled yearly target.
        "es2023" | "es2024" | "es2025" => Some(LibTarget::Es2022),
        "esnext" => Some(LibTarget::EsNext),
        _ => None,
    }
}

fn lib_name_to_virtual_path(name: &str) -> Option<&'static str> {
    Some(match name {
        "dom" | "dom.generated" => "lib.dom.d.ts",
        "dom.iterable" | "dom.iterable.generated" => "lib.dom.iterable.d.ts",
        "dom.asynciterable" | "dom.asynciterable.generated" => "lib.dom.asynciterable.d.ts",
        "es2015.core" => "lib.es2015.core.d.ts",
        "es2015.collection" => "lib.es2015.collection.d.ts",
        "es2015.generator" => "lib.es2015.generator.d.ts",
        "es2015.iterable" => "lib.es2015.iterable.d.ts",
        "es2015.promise" => "lib.es2015.promise.d.ts",
        "es2015.proxy" => "lib.es2015.proxy.d.ts",
        "es2015.reflect" => "lib.es2015.reflect.d.ts",
        "es2015.symbol" => "lib.es2015.symbol.d.ts",
        "es2015.symbol.wellknown" => "lib.es2015.symbol.wellknown.d.ts",
        "es2016.array.include" => "lib.es2016.array.include.d.ts",
        "es2016.intl" => "lib.es2016.intl.d.ts",
        "es2017.arraybuffer" => "lib.es2017.arraybuffer.d.ts",
        "es2017.date" => "lib.es2017.date.d.ts",
        "es2017.object" => "lib.es2017.object.d.ts",
        "es2017.sharedmemory" => "lib.es2017.sharedmemory.d.ts",
        "es2017.string" => "lib.es2017.string.d.ts",
        "es2017.intl" => "lib.es2017.intl.d.ts",
        "es2017.typedarrays" => "lib.es2017.typedarrays.d.ts",
        "es2018.asyncgenerator" => "lib.es2018.asyncgenerator.d.ts",
        "es2018.asynciterable" | "esnext.asynciterable" => "lib.es2018.asynciterable.d.ts",
        "es2018.intl" => "lib.es2018.intl.d.ts",
        "es2018.promise" => "lib.es2018.promise.d.ts",
        "es2018.regexp" => "lib.es2018.regexp.d.ts",
        "es2019.array" => "lib.es2019.array.d.ts",
        "es2019.object" => "lib.es2019.object.d.ts",
        "es2019.string" => "lib.es2019.string.d.ts",
        "es2019.symbol" | "esnext.symbol" => "lib.es2019.symbol.d.ts",
        "es2019.intl" => "lib.es2019.intl.d.ts",
        "es2020.bigint" | "esnext.bigint" => "lib.es2020.bigint.d.ts",
        "es2020.date" => "lib.es2020.date.d.ts",
        "es2020.promise" => "lib.es2020.promise.d.ts",
        "es2020.sharedmemory" => "lib.es2020.sharedmemory.d.ts",
        "es2020.string" => "lib.es2020.string.d.ts",
        "es2020.symbol.wellknown" => "lib.es2020.symbol.wellknown.d.ts",
        "es2020.intl" => "lib.es2020.intl.d.ts",
        "es2020.number" => "lib.es2020.number.d.ts",
        "es2021.promise" => "lib.es2021.promise.d.ts",
        "es2021.string" => "lib.es2021.string.d.ts",
        "es2021.weakref" | "esnext.weakref" => "lib.es2021.weakref.d.ts",
        "es2021.intl" => "lib.es2021.intl.d.ts",
        "es2022.array" => "lib.es2022.array.d.ts",
        "es2022.error" => "lib.es2022.error.d.ts",
        "es2022.intl" => "lib.es2022.intl.d.ts",
        "es2022.object" => "lib.es2022.object.d.ts",
        "es2022.regexp" => "lib.es2022.regexp.d.ts",
        "es2022.string" => "lib.es2022.string.d.ts",
        "esnext.collection" => "lib.esnext.collection.d.ts",
        "esnext.disposable" => "lib.esnext.disposable.d.ts",
        _ => return None,
    })
}

fn file_by_virtual_path(virtual_path: &str) -> Option<EmbeddedLibFile> {
    LIB_CATALOG
        .iter()
        .find(|entry| entry.file.virtual_path == virtual_path)
        .map(|entry| entry.file)
}

fn push_unique(files: &mut Vec<EmbeddedLibFile>, file: EmbeddedLibFile) {
    if !files
        .iter()
        .any(|existing| existing.virtual_path == file.virtual_path)
    {
        files.push(file);
    }
}

fn sort_by_catalog_order(files: &mut [EmbeddedLibFile]) {
    files.sort_by_key(|file| {
        LIB_CATALOG
            .iter()
            .position(|entry| entry.file.virtual_path == file.virtual_path)
            .unwrap_or(usize::MAX)
    });
}

const fn es_file(
    target: LibTarget,
    virtual_path: &'static str,
    contents: &'static str,
) -> LibCatalogEntry {
    LibCatalogEntry {
        file: EmbeddedLibFile {
            virtual_path,
            contents,
        },
        es_target: Some(target),
        default_host: false,
    }
}

const fn host_file(virtual_path: &'static str, contents: &'static str) -> LibCatalogEntry {
    LibCatalogEntry {
        file: EmbeddedLibFile {
            virtual_path,
            contents,
        },
        es_target: None,
        default_host: true,
    }
}

const LIB_CATALOG: &[LibCatalogEntry] = &[
    es_file(LibTarget::Es5, "lib.es5.d.ts", include_str!("lib/es5.d.ts")),
    es_file(
        LibTarget::Es2015,
        "lib.es2015.core.d.ts",
        include_str!("lib/es2015.core.d.ts"),
    ),
    es_file(
        LibTarget::Es2015,
        "lib.es2015.collection.d.ts",
        include_str!("lib/es2015.collection.d.ts"),
    ),
    es_file(
        LibTarget::Es2015,
        "lib.es2015.generator.d.ts",
        include_str!("lib/es2015.generator.d.ts"),
    ),
    es_file(
        LibTarget::Es2015,
        "lib.es2015.iterable.d.ts",
        include_str!("lib/es2015.iterable.d.ts"),
    ),
    es_file(
        LibTarget::Es2015,
        "lib.es2015.promise.d.ts",
        include_str!("lib/es2015.promise.d.ts"),
    ),
    es_file(
        LibTarget::Es2015,
        "lib.es2015.proxy.d.ts",
        include_str!("lib/es2015.proxy.d.ts"),
    ),
    es_file(
        LibTarget::Es2015,
        "lib.es2015.reflect.d.ts",
        include_str!("lib/es2015.reflect.d.ts"),
    ),
    es_file(
        LibTarget::Es2015,
        "lib.es2015.symbol.d.ts",
        include_str!("lib/es2015.symbol.d.ts"),
    ),
    es_file(
        LibTarget::Es2015,
        "lib.es2015.symbol.wellknown.d.ts",
        include_str!("lib/es2015.symbol.wellknown.d.ts"),
    ),
    es_file(
        LibTarget::Es2016,
        "lib.es2016.array.include.d.ts",
        include_str!("lib/es2016.array.include.d.ts"),
    ),
    es_file(
        LibTarget::Es2016,
        "lib.es2016.intl.d.ts",
        include_str!("lib/es2016.intl.d.ts"),
    ),
    es_file(
        LibTarget::Es2017,
        "lib.es2017.arraybuffer.d.ts",
        include_str!("lib/es2017.arraybuffer.d.ts"),
    ),
    es_file(
        LibTarget::Es2017,
        "lib.es2017.date.d.ts",
        include_str!("lib/es2017.date.d.ts"),
    ),
    es_file(
        LibTarget::Es2017,
        "lib.es2017.object.d.ts",
        include_str!("lib/es2017.object.d.ts"),
    ),
    es_file(
        LibTarget::Es2017,
        "lib.es2017.sharedmemory.d.ts",
        include_str!("lib/es2017.sharedmemory.d.ts"),
    ),
    es_file(
        LibTarget::Es2017,
        "lib.es2017.string.d.ts",
        include_str!("lib/es2017.string.d.ts"),
    ),
    es_file(
        LibTarget::Es2017,
        "lib.es2017.intl.d.ts",
        include_str!("lib/es2017.intl.d.ts"),
    ),
    es_file(
        LibTarget::Es2017,
        "lib.es2017.typedarrays.d.ts",
        include_str!("lib/es2017.typedarrays.d.ts"),
    ),
    es_file(
        LibTarget::Es2018,
        "lib.es2018.asyncgenerator.d.ts",
        include_str!("lib/es2018.asyncgenerator.d.ts"),
    ),
    es_file(
        LibTarget::Es2018,
        "lib.es2018.asynciterable.d.ts",
        include_str!("lib/es2018.asynciterable.d.ts"),
    ),
    es_file(
        LibTarget::Es2018,
        "lib.es2018.intl.d.ts",
        include_str!("lib/es2018.intl.d.ts"),
    ),
    es_file(
        LibTarget::Es2018,
        "lib.es2018.promise.d.ts",
        include_str!("lib/es2018.promise.d.ts"),
    ),
    es_file(
        LibTarget::Es2018,
        "lib.es2018.regexp.d.ts",
        include_str!("lib/es2018.regexp.d.ts"),
    ),
    es_file(
        LibTarget::Es2019,
        "lib.es2019.array.d.ts",
        include_str!("lib/es2019.array.d.ts"),
    ),
    es_file(
        LibTarget::Es2019,
        "lib.es2019.object.d.ts",
        include_str!("lib/es2019.object.d.ts"),
    ),
    es_file(
        LibTarget::Es2019,
        "lib.es2019.string.d.ts",
        include_str!("lib/es2019.string.d.ts"),
    ),
    es_file(
        LibTarget::Es2019,
        "lib.es2019.symbol.d.ts",
        include_str!("lib/es2019.symbol.d.ts"),
    ),
    es_file(
        LibTarget::Es2019,
        "lib.es2019.intl.d.ts",
        include_str!("lib/es2019.intl.d.ts"),
    ),
    es_file(
        LibTarget::Es2020,
        "lib.es2020.bigint.d.ts",
        include_str!("lib/es2020.bigint.d.ts"),
    ),
    es_file(
        LibTarget::Es2020,
        "lib.es2020.date.d.ts",
        include_str!("lib/es2020.date.d.ts"),
    ),
    es_file(
        LibTarget::Es2020,
        "lib.es2020.promise.d.ts",
        include_str!("lib/es2020.promise.d.ts"),
    ),
    es_file(
        LibTarget::Es2020,
        "lib.es2020.sharedmemory.d.ts",
        include_str!("lib/es2020.sharedmemory.d.ts"),
    ),
    es_file(
        LibTarget::Es2020,
        "lib.es2020.string.d.ts",
        include_str!("lib/es2020.string.d.ts"),
    ),
    es_file(
        LibTarget::Es2020,
        "lib.es2020.symbol.wellknown.d.ts",
        include_str!("lib/es2020.symbol.wellknown.d.ts"),
    ),
    es_file(
        LibTarget::Es2020,
        "lib.es2020.intl.d.ts",
        include_str!("lib/es2020.intl.d.ts"),
    ),
    es_file(
        LibTarget::Es2020,
        "lib.es2020.number.d.ts",
        include_str!("lib/es2020.number.d.ts"),
    ),
    es_file(
        LibTarget::Es2021,
        "lib.es2021.promise.d.ts",
        include_str!("lib/es2021.promise.d.ts"),
    ),
    es_file(
        LibTarget::Es2021,
        "lib.es2021.string.d.ts",
        include_str!("lib/es2021.string.d.ts"),
    ),
    es_file(
        LibTarget::Es2021,
        "lib.es2021.weakref.d.ts",
        include_str!("lib/es2021.weakref.d.ts"),
    ),
    es_file(
        LibTarget::Es2021,
        "lib.es2021.intl.d.ts",
        include_str!("lib/es2021.intl.d.ts"),
    ),
    es_file(
        LibTarget::Es2022,
        "lib.es2022.array.d.ts",
        include_str!("lib/es2022.array.d.ts"),
    ),
    es_file(
        LibTarget::Es2022,
        "lib.es2022.error.d.ts",
        include_str!("lib/es2022.error.d.ts"),
    ),
    es_file(
        LibTarget::Es2022,
        "lib.es2022.intl.d.ts",
        include_str!("lib/es2022.intl.d.ts"),
    ),
    es_file(
        LibTarget::Es2022,
        "lib.es2022.object.d.ts",
        include_str!("lib/es2022.object.d.ts"),
    ),
    es_file(
        LibTarget::Es2022,
        "lib.es2022.string.d.ts",
        include_str!("lib/es2022.string.d.ts"),
    ),
    es_file(
        LibTarget::Es2022,
        "lib.es2022.regexp.d.ts",
        include_str!("lib/es2022.regexp.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.collection.d.ts",
        include_str!("lib/esnext.collection.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.disposable.d.ts",
        include_str!("lib/esnext.disposable.d.ts"),
    ),
    host_file("lib.dom.d.ts", include_str!("lib/dom.generated.d.ts")),
    host_file(
        "lib.dom.iterable.d.ts",
        include_str!("lib/dom.iterable.generated.d.ts"),
    ),
    host_file(
        "lib.dom.asynciterable.d.ts",
        include_str!("lib/dom.asynciterable.generated.d.ts"),
    ),
];

#[cfg(test)]
mod tests {
    use super::*;

    fn paths(files: &[EmbeddedLibFile]) -> Vec<&'static str> {
        files.iter().map(|file| file.virtual_path).collect()
    }

    #[test]
    fn es2015_target_excludes_newer_libs() {
        let files = resolve_lib_files(&LibSelection::DefaultTarget(LibTarget::Es2015)).unwrap();
        let paths = paths(&files);

        assert!(paths.contains(&"lib.es5.d.ts"));
        assert!(paths.contains(&"lib.es2015.promise.d.ts"));
        assert!(!paths.contains(&"lib.es2016.array.include.d.ts"));
        assert!(!paths.contains(&"lib.es2020.promise.d.ts"));
    }

    #[test]
    fn es2022_target_includes_previous_years() {
        let files = resolve_lib_files(&LibSelection::DefaultTarget(LibTarget::Es2022)).unwrap();
        let paths = paths(&files);

        assert!(paths.contains(&"lib.es5.d.ts"));
        assert!(paths.contains(&"lib.es2015.promise.d.ts"));
        assert!(paths.contains(&"lib.es2020.promise.d.ts"));
        assert!(paths.contains(&"lib.es2021.weakref.d.ts"));
        assert!(paths.contains(&"lib.es2022.array.d.ts"));
        assert!(!paths.contains(&"lib.esnext.disposable.d.ts"));
    }

    #[test]
    fn esnext_target_includes_latest_libs() {
        let files = resolve_lib_files(&LibSelection::DefaultTarget(LibTarget::EsNext)).unwrap();
        let paths = paths(&files);

        assert!(paths.contains(&"lib.es2022.array.d.ts"));
        assert!(paths.contains(&"lib.esnext.collection.d.ts"));
        assert!(paths.contains(&"lib.esnext.disposable.d.ts"));
    }

    #[test]
    fn explicit_libs_do_not_include_target_defaults() {
        let files = resolve_lib_files(&LibSelection::Explicit(vec![
            "dom".to_string(),
            "es5".to_string(),
            "es2015.promise".to_string(),
        ]))
        .unwrap();
        let paths = paths(&files);

        assert_eq!(
            paths,
            vec!["lib.es5.d.ts", "lib.es2015.promise.d.ts", "lib.dom.d.ts"]
        );
    }
}
