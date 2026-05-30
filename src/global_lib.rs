//! Embedded TypeScript standard library (`.d.ts`) declarations.
//!
//! The files under `src/lib/` are copied verbatim from the TypeScript compiler.
//! They are embedded into the binary so the checker can load the default global
//! library without touching the file system.
//!
//! TODO: support selecting the library year/target. For now we always load the
//! es2015 family. `es2015.d.ts` itself is a reference-only index and is not
//! included here; the concrete file list is hardcoded below.

/// The default global library files, as `(virtual_path, contents)` pairs.
pub(crate) const DEFAULT_LIB_FILES: &[(&str, &str)] = &[
    ("lib.es5.d.ts", include_str!("lib/es5.d.ts")),
    ("lib.es2015.core.d.ts", include_str!("lib/es2015.core.d.ts")),
    (
        "lib.es2015.collection.d.ts",
        include_str!("lib/es2015.collection.d.ts"),
    ),
    (
        "lib.es2015.iterable.d.ts",
        include_str!("lib/es2015.iterable.d.ts"),
    ),
    (
        "lib.es2015.generator.d.ts",
        include_str!("lib/es2015.generator.d.ts"),
    ),
    (
        "lib.es2015.promise.d.ts",
        include_str!("lib/es2015.promise.d.ts"),
    ),
    (
        "lib.es2015.proxy.d.ts",
        include_str!("lib/es2015.proxy.d.ts"),
    ),
    (
        "lib.es2015.reflect.d.ts",
        include_str!("lib/es2015.reflect.d.ts"),
    ),
    (
        "lib.es2015.symbol.d.ts",
        include_str!("lib/es2015.symbol.d.ts"),
    ),
    (
        "lib.es2015.symbol.wellknown.d.ts",
        include_str!("lib/es2015.symbol.wellknown.d.ts"),
    ),
    ("lib.dom.d.ts", include_str!("lib/dom.generated.d.ts")),
    (
        "lib.dom.iterable.d.ts",
        include_str!("lib/dom.iterable.generated.d.ts"),
    ),
    (
        "lib.dom.asynciterable.d.ts",
        include_str!("lib/dom.asynciterable.generated.d.ts"),
    ),
];
