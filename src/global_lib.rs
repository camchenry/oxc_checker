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

use std::{error::Error, fmt, str::FromStr};

/// ECMAScript language level used to select the default standard libraries.
///
/// ```
/// use oxc_checker::LibTarget;
///
/// assert_eq!("es2022".parse(), Ok(LibTarget::Es2022));
/// assert_eq!("latest".parse(), Ok(LibTarget::EsNext));
/// ```
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum LibTarget {
    /// ECMAScript 5 (also used for the legacy `es3` target).
    Es5,
    /// ECMAScript 2015 (`es6`).
    Es2015,
    /// ECMAScript 2016 (`es7`).
    Es2016,
    /// ECMAScript 2017.
    Es2017,
    /// ECMAScript 2018.
    Es2018,
    /// ECMAScript 2019.
    Es2019,
    /// ECMAScript 2020.
    Es2020,
    /// ECMAScript 2021.
    Es2021,
    /// ECMAScript 2022.
    Es2022,
    /// ECMAScript 2023.
    Es2023,
    /// ECMAScript 2024.
    Es2024,
    /// ECMAScript 2025.
    Es2025,
    /// The latest embedded ECMAScript libraries.
    EsNext,
}

impl FromStr for LibTarget {
    type Err = StandardLibrarySelectionError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let value = value.trim().to_ascii_lowercase();
        match value.as_str() {
            "es3" | "es5" => Ok(Self::Es5),
            "es6" | "es2015" => Ok(Self::Es2015),
            "es7" | "es2016" => Ok(Self::Es2016),
            "es2017" => Ok(Self::Es2017),
            "es2018" => Ok(Self::Es2018),
            "es2019" => Ok(Self::Es2019),
            "es2020" => Ok(Self::Es2020),
            "es2021" => Ok(Self::Es2021),
            "es2022" => Ok(Self::Es2022),
            "es2023" => Ok(Self::Es2023),
            "es2024" => Ok(Self::Es2024),
            "es2025" => Ok(Self::Es2025),
            "esnext" | "latest" => Ok(Self::EsNext),
            _ => Err(StandardLibrarySelectionError::UnsupportedTarget { target: value }),
        }
    }
}

/// A validated selection of embedded TypeScript standard-library files.
///
/// Use [`Self::for_target`] for TypeScript's default target-based library set,
/// or [`Self::from_lib_names`] for an explicit `lib` configuration.
///
/// ```
/// use oxc_checker::{LibTarget, StandardLibrarySelection};
///
/// let defaults = StandardLibrarySelection::for_target(LibTarget::Es2022);
/// let explicit = StandardLibrarySelection::from_lib_names(["es2022", "dom"])?;
/// # Ok::<(), oxc_checker::StandardLibrarySelectionError>(())
/// ```
#[derive(Clone, Eq, PartialEq)]
pub struct StandardLibrarySelection {
    files: Vec<EmbeddedLibFile>,
}

impl fmt::Debug for StandardLibrarySelection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("StandardLibrarySelection")
            .field(
                "files",
                &self
                    .files
                    .iter()
                    .map(|file| file.virtual_path)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl StandardLibrarySelection {
    /// Select the default language and host libraries for `target`.
    #[must_use]
    pub fn for_target(target: LibTarget) -> Self {
        let mut files = Vec::new();
        append_target_files(&mut files, target);
        append_default_host_files(&mut files);
        Self { files }
    }

    /// Select an explicit list of TypeScript `lib` names.
    ///
    /// Names are case-insensitive and may use forms such as `dom`,
    /// `lib.es2022.d.ts`, or `es2022.full`. An empty iterator selects no files.
    ///
    /// # Errors
    ///
    /// Returns [`StandardLibrarySelectionError::UnsupportedLibrary`] when a
    /// name does not identify an embedded standard library.
    pub fn from_lib_names<I, S>(names: I) -> Result<Self, StandardLibrarySelectionError>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut files = Vec::new();
        for name in names {
            append_lib_name(&mut files, name.as_ref())?;
        }
        sort_by_catalog_order(&mut files);
        Ok(Self { files })
    }
}

impl Default for StandardLibrarySelection {
    fn default() -> Self {
        Self::for_target(DEFAULT_LIB_TARGET)
    }
}

impl From<LibTarget> for StandardLibrarySelection {
    fn from(target: LibTarget) -> Self {
        Self::for_target(target)
    }
}

/// An invalid standard-library target or explicit library name.
///
/// This error is returned while configuration is constructed, before a
/// [`crate::program::ProgramStore`] build starts.
///
/// ```
/// use oxc_checker::{StandardLibrarySelection, StandardLibrarySelectionError};
///
/// let error = StandardLibrarySelection::from_lib_names(["not-a-lib"]).unwrap_err();
/// assert!(matches!(
///     error,
///     StandardLibrarySelectionError::UnsupportedLibrary { .. }
/// ));
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum StandardLibrarySelectionError {
    /// The target name is not recognized.
    UnsupportedTarget {
        /// The normalized target supplied by the caller.
        target: String,
    },
    /// An explicit library name is not available in the embedded catalog.
    UnsupportedLibrary {
        /// The library name supplied by the caller.
        name: String,
    },
}

impl fmt::Display for StandardLibrarySelectionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedTarget { target } => {
                write!(formatter, "unsupported target `{target}`")
            }
            Self::UnsupportedLibrary { name } => write!(formatter, "unsupported lib `{name}`"),
        }
    }
}

impl Error for StandardLibrarySelectionError {}

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
pub(crate) fn default_lib_files() -> Vec<EmbeddedLibFile> {
    StandardLibrarySelection::default().files
}

pub(crate) fn resolve_lib_files(selection: &StandardLibrarySelection) -> &[EmbeddedLibFile] {
    &selection.files
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

fn append_lib_name(
    files: &mut Vec<EmbeddedLibFile>,
    name: &str,
) -> Result<(), StandardLibrarySelectionError> {
    let normalized = normalize_lib_name(name);
    if let Some(target) = normalized
        .strip_suffix(".full")
        .and_then(aggregate_lib_target)
    {
        append_target_files(files, target);
        append_default_host_files(files);
        return Ok(());
    }
    if let Some(target) = aggregate_lib_target(&normalized) {
        append_target_files(files, target);
        return Ok(());
    }

    let Some(virtual_path) = lib_name_to_virtual_path(&normalized) else {
        return Err(StandardLibrarySelectionError::UnsupportedLibrary {
            name: name.trim().to_string(),
        });
    };
    let Some(file) = file_by_virtual_path(virtual_path) else {
        return Err(StandardLibrarySelectionError::UnsupportedLibrary {
            name: name.trim().to_string(),
        });
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
        "es2023" => Some(LibTarget::Es2023),
        "es2024" => Some(LibTarget::Es2024),
        "es2025" => Some(LibTarget::Es2025),
        "esnext" => Some(LibTarget::EsNext),
        _ => None,
    }
}

fn lib_name_to_virtual_path(name: &str) -> Option<&'static str> {
    Some(match name {
        "dom" | "dom.generated" => "lib.dom.d.ts",
        "dom.iterable" | "dom.iterable.generated" => "lib.dom.iterable.d.ts",
        "dom.asynciterable" | "dom.asynciterable.generated" => "lib.dom.asynciterable.d.ts",
        "webworker" | "webworker.generated" => "lib.webworker.d.ts",
        "webworker.importscripts" => "lib.webworker.importscripts.d.ts",
        "webworker.iterable" | "webworker.iterable.generated" => "lib.webworker.iterable.d.ts",
        "webworker.asynciterable" | "webworker.asynciterable.generated" => {
            "lib.webworker.asynciterable.d.ts"
        }
        "scripthost" => "lib.scripthost.d.ts",
        "decorators" => "lib.decorators.d.ts",
        "decorators.legacy" => "lib.decorators.legacy.d.ts",
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
        "es2023.array" => "lib.es2023.array.d.ts",
        "es2023.collection" => "lib.es2023.collection.d.ts",
        "es2023.intl" => "lib.es2023.intl.d.ts",
        "es2024.arraybuffer" => "lib.es2024.arraybuffer.d.ts",
        "es2024.collection" => "lib.es2024.collection.d.ts",
        "es2024.object" => "lib.es2024.object.d.ts",
        "es2024.promise" => "lib.es2024.promise.d.ts",
        "es2024.regexp" => "lib.es2024.regexp.d.ts",
        "es2024.sharedmemory" => "lib.es2024.sharedmemory.d.ts",
        "es2024.string" => "lib.es2024.string.d.ts",
        "es2025.collection" => "lib.es2025.collection.d.ts",
        "es2025.float16" => "lib.es2025.float16.d.ts",
        "es2025.intl" => "lib.es2025.intl.d.ts",
        "es2025.iterator" => "lib.es2025.iterator.d.ts",
        "es2025.promise" => "lib.es2025.promise.d.ts",
        "es2025.regexp" => "lib.es2025.regexp.d.ts",
        "esnext.array" => "lib.esnext.array.d.ts",
        "esnext.collection" => "lib.esnext.collection.d.ts",
        "esnext.date" => "lib.esnext.date.d.ts",
        "esnext.decorators" => "lib.esnext.decorators.d.ts",
        "esnext.disposable" => "lib.esnext.disposable.d.ts",
        "esnext.error" => "lib.esnext.error.d.ts",
        "esnext.intl" => "lib.esnext.intl.d.ts",
        "esnext.sharedmemory" => "lib.esnext.sharedmemory.d.ts",
        "esnext.temporal" => "lib.esnext.temporal.d.ts",
        "esnext.typedarrays" => "lib.esnext.typedarrays.d.ts",
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

const fn plain_file(virtual_path: &'static str, contents: &'static str) -> LibCatalogEntry {
    LibCatalogEntry {
        file: EmbeddedLibFile {
            virtual_path,
            contents,
        },
        es_target: None,
        default_host: false,
    }
}

const LIB_CATALOG: &[LibCatalogEntry] = &[
    es_file(
        LibTarget::Es5,
        "lib.decorators.d.ts",
        include_str!("lib/decorators.d.ts"),
    ),
    es_file(
        LibTarget::Es5,
        "lib.decorators.legacy.d.ts",
        include_str!("lib/decorators.legacy.d.ts"),
    ),
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
        LibTarget::Es2023,
        "lib.es2023.array.d.ts",
        include_str!("lib/es2023.array.d.ts"),
    ),
    es_file(
        LibTarget::Es2023,
        "lib.es2023.collection.d.ts",
        include_str!("lib/es2023.collection.d.ts"),
    ),
    es_file(
        LibTarget::Es2023,
        "lib.es2023.intl.d.ts",
        include_str!("lib/es2023.intl.d.ts"),
    ),
    es_file(
        LibTarget::Es2024,
        "lib.es2024.arraybuffer.d.ts",
        include_str!("lib/es2024.arraybuffer.d.ts"),
    ),
    es_file(
        LibTarget::Es2024,
        "lib.es2024.collection.d.ts",
        include_str!("lib/es2024.collection.d.ts"),
    ),
    es_file(
        LibTarget::Es2024,
        "lib.es2024.object.d.ts",
        include_str!("lib/es2024.object.d.ts"),
    ),
    es_file(
        LibTarget::Es2024,
        "lib.es2024.promise.d.ts",
        include_str!("lib/es2024.promise.d.ts"),
    ),
    es_file(
        LibTarget::Es2024,
        "lib.es2024.regexp.d.ts",
        include_str!("lib/es2024.regexp.d.ts"),
    ),
    es_file(
        LibTarget::Es2024,
        "lib.es2024.sharedmemory.d.ts",
        include_str!("lib/es2024.sharedmemory.d.ts"),
    ),
    es_file(
        LibTarget::Es2024,
        "lib.es2024.string.d.ts",
        include_str!("lib/es2024.string.d.ts"),
    ),
    es_file(
        LibTarget::Es2025,
        "lib.es2025.collection.d.ts",
        include_str!("lib/es2025.collection.d.ts"),
    ),
    es_file(
        LibTarget::Es2025,
        "lib.es2025.float16.d.ts",
        include_str!("lib/es2025.float16.d.ts"),
    ),
    es_file(
        LibTarget::Es2025,
        "lib.es2025.intl.d.ts",
        include_str!("lib/es2025.intl.d.ts"),
    ),
    es_file(
        LibTarget::Es2025,
        "lib.es2025.iterator.d.ts",
        include_str!("lib/es2025.iterator.d.ts"),
    ),
    es_file(
        LibTarget::Es2025,
        "lib.es2025.promise.d.ts",
        include_str!("lib/es2025.promise.d.ts"),
    ),
    es_file(
        LibTarget::Es2025,
        "lib.es2025.regexp.d.ts",
        include_str!("lib/es2025.regexp.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.intl.d.ts",
        include_str!("lib/esnext.intl.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.collection.d.ts",
        include_str!("lib/esnext.collection.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.decorators.d.ts",
        include_str!("lib/esnext.decorators.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.disposable.d.ts",
        include_str!("lib/esnext.disposable.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.array.d.ts",
        include_str!("lib/esnext.array.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.error.d.ts",
        include_str!("lib/esnext.error.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.sharedmemory.d.ts",
        include_str!("lib/esnext.sharedmemory.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.typedarrays.d.ts",
        include_str!("lib/esnext.typedarrays.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.temporal.d.ts",
        include_str!("lib/esnext.temporal.d.ts"),
    ),
    es_file(
        LibTarget::EsNext,
        "lib.esnext.date.d.ts",
        include_str!("lib/esnext.date.d.ts"),
    ),
    host_file("lib.dom.d.ts", include_str!("lib/dom.generated.d.ts")),
    host_file(
        "lib.webworker.importscripts.d.ts",
        include_str!("lib/webworker.importscripts.d.ts"),
    ),
    host_file("lib.scripthost.d.ts", include_str!("lib/scripthost.d.ts")),
    host_file(
        "lib.dom.iterable.d.ts",
        include_str!("lib/dom.iterable.generated.d.ts"),
    ),
    host_file(
        "lib.dom.asynciterable.d.ts",
        include_str!("lib/dom.asynciterable.generated.d.ts"),
    ),
    plain_file(
        "lib.webworker.d.ts",
        include_str!("lib/webworker.generated.d.ts"),
    ),
    plain_file(
        "lib.webworker.iterable.d.ts",
        include_str!("lib/webworker.iterable.generated.d.ts"),
    ),
    plain_file(
        "lib.webworker.asynciterable.d.ts",
        include_str!("lib/webworker.asynciterable.generated.d.ts"),
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
        let selection = StandardLibrarySelection::for_target(LibTarget::Es2015);
        let files = resolve_lib_files(&selection);
        let paths = paths(files);

        assert!(paths.contains(&"lib.es5.d.ts"));
        assert!(paths.contains(&"lib.es2015.promise.d.ts"));
        assert!(!paths.contains(&"lib.es2016.array.include.d.ts"));
        assert!(!paths.contains(&"lib.es2020.promise.d.ts"));
    }

    #[test]
    fn es2022_target_includes_previous_years() {
        let selection = StandardLibrarySelection::for_target(LibTarget::Es2022);
        let files = resolve_lib_files(&selection);
        let paths = paths(files);

        assert!(paths.contains(&"lib.es5.d.ts"));
        assert!(paths.contains(&"lib.es2015.promise.d.ts"));
        assert!(paths.contains(&"lib.es2020.promise.d.ts"));
        assert!(paths.contains(&"lib.es2021.weakref.d.ts"));
        assert!(paths.contains(&"lib.es2022.array.d.ts"));
        assert!(!paths.contains(&"lib.esnext.disposable.d.ts"));
    }

    #[test]
    fn esnext_target_includes_latest_libs() {
        let selection = StandardLibrarySelection::for_target(LibTarget::EsNext);
        let files = resolve_lib_files(&selection);
        let paths = paths(files);

        assert!(paths.contains(&"lib.es2025.iterator.d.ts"));
        assert!(paths.contains(&"lib.esnext.array.d.ts"));
        assert!(paths.contains(&"lib.esnext.collection.d.ts"));
        assert!(paths.contains(&"lib.esnext.date.d.ts"));
        assert!(paths.contains(&"lib.esnext.decorators.d.ts"));
        assert!(paths.contains(&"lib.esnext.disposable.d.ts"));
        assert!(paths.contains(&"lib.esnext.error.d.ts"));
        assert!(paths.contains(&"lib.esnext.intl.d.ts"));
        assert!(paths.contains(&"lib.esnext.sharedmemory.d.ts"));
        assert!(paths.contains(&"lib.esnext.temporal.d.ts"));
        assert!(paths.contains(&"lib.esnext.typedarrays.d.ts"));
    }

    #[test]
    fn explicit_libs_do_not_include_target_defaults() {
        let selection =
            StandardLibrarySelection::from_lib_names(["dom", "es5", "es2015.promise"]).unwrap();
        let files = resolve_lib_files(&selection);
        let paths = paths(files);

        assert_eq!(
            paths,
            vec![
                "lib.decorators.d.ts",
                "lib.decorators.legacy.d.ts",
                "lib.es5.d.ts",
                "lib.es2015.promise.d.ts",
                "lib.dom.d.ts"
            ]
        );
    }

    #[test]
    fn full_lib_includes_default_hosts() {
        let selection = StandardLibrarySelection::from_lib_names(["es2025.full"]).unwrap();
        let files = resolve_lib_files(&selection);
        let paths = paths(files);

        assert!(paths.contains(&"lib.es2025.regexp.d.ts"));
        assert!(paths.contains(&"lib.dom.d.ts"));
        assert!(paths.contains(&"lib.webworker.importscripts.d.ts"));
        assert!(paths.contains(&"lib.scripthost.d.ts"));
        assert!(!paths.contains(&"lib.esnext.array.d.ts"));
    }

    #[test]
    fn explicit_host_libs_are_supported() {
        let selection = StandardLibrarySelection::from_lib_names([
            "webworker",
            "webworker.iterable",
            "webworker.asynciterable",
        ])
        .unwrap();
        let files = resolve_lib_files(&selection);

        assert_eq!(
            paths(files),
            vec![
                "lib.webworker.d.ts",
                "lib.webworker.iterable.d.ts",
                "lib.webworker.asynciterable.d.ts"
            ]
        );
    }

    #[test]
    fn invalid_names_are_rejected_during_selection_construction() {
        assert_eq!(
            "es2099".parse::<LibTarget>(),
            Err(StandardLibrarySelectionError::UnsupportedTarget {
                target: "es2099".to_string()
            })
        );
        assert_eq!(
            StandardLibrarySelection::from_lib_names(["dom", "not-a-lib"]),
            Err(StandardLibrarySelectionError::UnsupportedLibrary {
                name: "not-a-lib".to_string()
            })
        );
    }
}
