//! Embedded TypeScript standard library (`.d.ts`) declarations.
//!
//! The files under `src/lib/` are copied verbatim from the TypeScript compiler.
//! They are embedded into the binary so the checker can load the default global
//! library without touching the file system.
//!
//! TODO: support selecting the library year/target. For now we always load the
//! ES2020 family. `es20xx.d.ts` and `es20xx.full.d.ts` files are reference-only
//! indexes and are not included here; the concrete file list is hardcoded below.

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
    (
        "lib.es2016.array.include.d.ts",
        include_str!("lib/es2016.array.include.d.ts"),
    ),
    ("lib.es2016.intl.d.ts", include_str!("lib/es2016.intl.d.ts")),
    (
        "lib.es2017.arraybuffer.d.ts",
        include_str!("lib/es2017.arraybuffer.d.ts"),
    ),
    ("lib.es2017.date.d.ts", include_str!("lib/es2017.date.d.ts")),
    ("lib.es2017.intl.d.ts", include_str!("lib/es2017.intl.d.ts")),
    (
        "lib.es2017.object.d.ts",
        include_str!("lib/es2017.object.d.ts"),
    ),
    (
        "lib.es2017.sharedmemory.d.ts",
        include_str!("lib/es2017.sharedmemory.d.ts"),
    ),
    (
        "lib.es2017.string.d.ts",
        include_str!("lib/es2017.string.d.ts"),
    ),
    (
        "lib.es2017.typedarrays.d.ts",
        include_str!("lib/es2017.typedarrays.d.ts"),
    ),
    (
        "lib.es2018.asynciterable.d.ts",
        include_str!("lib/es2018.asynciterable.d.ts"),
    ),
    (
        "lib.es2018.asyncgenerator.d.ts",
        include_str!("lib/es2018.asyncgenerator.d.ts"),
    ),
    (
        "lib.es2018.promise.d.ts",
        include_str!("lib/es2018.promise.d.ts"),
    ),
    (
        "lib.es2018.regexp.d.ts",
        include_str!("lib/es2018.regexp.d.ts"),
    ),
    ("lib.es2018.intl.d.ts", include_str!("lib/es2018.intl.d.ts")),
    (
        "lib.es2019.array.d.ts",
        include_str!("lib/es2019.array.d.ts"),
    ),
    (
        "lib.es2019.object.d.ts",
        include_str!("lib/es2019.object.d.ts"),
    ),
    (
        "lib.es2019.string.d.ts",
        include_str!("lib/es2019.string.d.ts"),
    ),
    (
        "lib.es2019.symbol.d.ts",
        include_str!("lib/es2019.symbol.d.ts"),
    ),
    ("lib.es2019.intl.d.ts", include_str!("lib/es2019.intl.d.ts")),
    (
        "lib.es2020.bigint.d.ts",
        include_str!("lib/es2020.bigint.d.ts"),
    ),
    ("lib.es2020.date.d.ts", include_str!("lib/es2020.date.d.ts")),
    (
        "lib.es2020.number.d.ts",
        include_str!("lib/es2020.number.d.ts"),
    ),
    (
        "lib.es2020.promise.d.ts",
        include_str!("lib/es2020.promise.d.ts"),
    ),
    (
        "lib.es2020.sharedmemory.d.ts",
        include_str!("lib/es2020.sharedmemory.d.ts"),
    ),
    (
        "lib.es2020.string.d.ts",
        include_str!("lib/es2020.string.d.ts"),
    ),
    (
        "lib.es2020.symbol.wellknown.d.ts",
        include_str!("lib/es2020.symbol.wellknown.d.ts"),
    ),
    ("lib.es2020.intl.d.ts", include_str!("lib/es2020.intl.d.ts")),
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
