# TypeScript Checker References

This document collects notes on related TypeScript compiler/checker projects that are useful references for `oxc_checker`.

Repository: <https://github.com/microsoft/typescript-go>

`typescript-go` is Microsoft's native Go port of TypeScript. It is the most authoritative comparison point because it is intended to become part of `microsoft/TypeScript`.

The README describes the project as a TypeScript 7 preview with many core features marked as done, including program creation, parsing/scanning, command-line and `tsconfig.json` parsing, type resolution, type checking, JavaScript/JSDoc handling, JSX, declaration emit, JavaScript emit, build mode/project references, and incremental build. Language service support is in progress, and the API is not ready.

Useful reference files and directories:

- [`README.md`](https://github.com/microsoft/typescript-go/blob/main/README.md) - project 00atus, preview usage, and feature-completion table.
- [`go.mod`](https://github.com/microsoft/typescript-go/blob/main/go.mod) - Go module metadata and dependencies.
- [`internal/ast/ast.go`](https://github.com/microsoft/typescript-go/blob/main/internal/ast/ast.go) - core AST definitions.
- [`internal/ast/symbol.go`](https://github.com/microsoft/typescript-go/blob/main/internal/ast/symbol.go) - symbol representation.
- [`internal/ast/symbolflags.go`](https://github.com/microsoft/typescript-go/blob/main/internal/ast/symbolflags.go) - symbol flag definitions.
- [`internal/checker/checker.go`](https://github.com/microsoft/typescript-go/blob/main/internal/checker/checker.go) - central checker implementation.
- [`internal/checker/types.go`](https://github.com/microsoft/typescript-go/blob/main/internal/checker/types.go) - checker type representation.
- [`internal/checker/relater.go`](https://github.com/microsoft/typescript-go/blob/main/internal/checker/relater.go) - type relationship and assignability logic.
- [`internal/checker/inference.go`](https://github.com/microsoft/typescript-go/blob/main/internal/checker/inference.go) - type inference machinery.
- [`internal/checker/flow.go`](https://github.com/microsoft/typescript-go/blob/main/internal/checker/flow.go) - flow-sensitive type analysis.
- [`internal/checker/services.go`](https://github.com/microsoft/typescript-go/blob/main/internal/checker/services.go) - checker-facing services APIs.
- [`internal/compiler/program.go`](https://github.com/microsoft/typescript-go/blob/main/internal/compiler/program.go) - program construction and compiler orchestration.
- [`internal/compiler/checkerpool.go`](https://github.com/microsoft/typescript-go/blob/main/internal/compiler/checkerpool.go) - checker lifecycle/pooling.
- [`internal/compiler/emitter.go`](https://github.com/microsoft/typescript-go/blob/main/internal/compiler/emitter.go) - JavaScript emit integration.

What `oxc_checker` can learn from it:

- Treat TypeScript compatibility as the primary correctness target.
- Separate program construction, checker state, relation logic, inference, flow analysis, and emit-facing APIs.
- Use conformance-style tests that compare diagnostics, locations, messages, and printed types against TypeScript behavior.
- Keep the public API intentionally conservative until the internal checker model stabilizes.

Local architecture map:

| TypeScript-Go concept | TypeScript-Go reference | `oxc_checker` analogue | Notes |
| --- | --- | --- | --- |
| Program construction and file graph | `internal/compiler/program.go` | `src/program.rs` `ProgramStore`, `ProgramStoreBuilder`, `ProgramHost` | Local code keeps parsing, Oxc semantic data, source text, and module edges together. It does not yet model tsconfig options, project references, diagnostics orchestration, emit, or incremental updates. |
| Checker state and query API | `internal/checker/checker.go`, `internal/checker/services.go` | `CheckerReturn`, `Checker` trait | Local checker state is still compact and store-backed. The goal is to keep query names close to TypeScript-Go so behavior comparisons have obvious entry points. |
| Type representation | `internal/checker/types.go` | `src/types.rs` `Ty`, `TyFunction`, `TyObject`, `Signature`, `IndexInfo` | Local types are arena-backed enum values today rather than `TypeId` plus `TypeFlags`/`ObjectFlags`. Keep this simpler representation until richer structural behavior needs a flag/id model. |
| Type relations and assignability | `internal/checker/relater.go` | planned `src/checker/relations.rs`; current `Checker::is_assignable_to` hook | This should become a first-class subsystem before broad checking diagnostics are added. Start with small, explicit relation rules and keep diagnostics separate. |
| Type inference | `internal/checker/inference.go` | current generic substitution and call inference helpers; planned `src/checker/inference.rs` | Current support is deliberately narrow. Use TypeScript-Go terminology such as inference context and type mapper when the implementation grows. |
| Flow-sensitive narrowing | `internal/checker/flow.go` | planned `src/checker/flow.rs` | No full local flow model exists yet. Add the module as a boundary only when real narrowing behavior lands. |
| Conformance baselines | `testdata/baselines`, test tasks in `Herebyfile.mjs` | `src/conformance.rs`, `tests/conformance/tsc_type_extractor.ts`, snapshot files | Local harness compares identifier type strings from TypeScript's compiler API against OXC records. This is closer to a type-query oracle than tsgo's full diagnostic and emit baselines. |

Intentional differences:

- Oxc provides parsing and semantic binding; do not port TypeScript-Go's binder wholesale.
- This crate is an API-oriented type information layer, not a replacement CLI, emitter, language service, or watch/build system.
- Full TypeScript compiler options, library loading, project references, JavaScript/JSDoc semantics, JSX semantics, and incremental checking are outside the initial alignment pass.
- Prefer small behavior-preserving module boundaries first; use TypeScript-Go as vocabulary and behavioral reference rather than source to copy.

## `mohsen1/tsz`

Repository: <https://github.com/mohsen1/tsz>

`tsz` is a performance-first TypeScript compiler in Rust. Its goal is a correct, fast, drop-in replacement for `tsc`, with native and WASM targets. The project describes its architecture as a sound core solver with a compatibility layer for TypeScript behavior.

The README reports pre-release status and notes that diagnostics, inference, and emit may differ from TypeScript today. It also reports TypeScript conformance progress using diagnostic fingerprint comparison, plus JavaScript/declaration emit baseline comparison and fourslash language-service coverage.

Useful reference files and directories:

- [`README.md`](https://github.com/mohsen1/tsz/blob/main/README.md) - project goals, status, performance notes, and compatibility metrics.
- [`Cargo.toml`](https://github.com/mohsen1/tsz/blob/main/Cargo.toml) - Rust workspace layout, shared dependencies, lint settings, and build profiles.
- [`crates/tsz-scanner`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-scanner) - scanner crate.
- [`crates/tsz-parser`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-parser) - parser crate.
- [`crates/tsz-binder`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-binder) - binder and symbol-building crate.
- [`crates/tsz-binder/src/symbols.rs`](https://github.com/mohsen1/tsz/blob/main/crates/tsz-binder/src/symbols.rs) - symbol representation and binder symbol logic.
- [`crates/tsz-solver`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-solver) - solver crate for types, relations, inference, narrowing, flow analysis, and type queries.
- [`crates/tsz-solver/src/types.rs`](https://github.com/mohsen1/tsz/blob/main/crates/tsz-solver/src/types.rs) - interned structural type representation using lightweight `TypeId` handles.
- [`crates/tsz-solver/src/relations`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-solver/src/relations) - type relation logic.
- [`crates/tsz-solver/src/inference`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-solver/src/inference) - inference support.
- [`crates/tsz-solver/src/narrowing`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-solver/src/narrowing) - narrowing support.
- [`crates/tsz-checker`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-checker) - checker crate.
- [`crates/tsz-checker/src/lib.rs`](https://github.com/mohsen1/tsz/blob/main/crates/tsz-checker/src/lib.rs) - checker module organization and top-level exports.
- [`crates/tsz-checker/src/dispatch.rs`](https://github.com/mohsen1/tsz/blob/main/crates/tsz-checker/src/dispatch.rs) - large dispatch/checking implementation.
- [`crates/tsz-checker/src/assignability`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-checker/src/assignability) - checker-facing assignability support.
- [`crates/tsz-emitter`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-emitter) - JavaScript/declaration emit support.
- [`crates/tsz-lsp`](https://github.com/mohsen1/tsz/tree/main/crates/tsz-lsp) - language server support.
- [`crates/conformance`](https://github.com/mohsen1/tsz/tree/main/crates/conformance) - TypeScript compatibility/conformance tooling.

What `oxc_checker` could learn from it:

- A Rust checker benefits from explicit crate/module boundaries between parsing, binding, solving, checking, emitting, and LSP support.
- A compact interned `TypeId`-style type representation can keep checker APIs lightweight while supporting richer type structures internally.
- A relation/assignability layer should be a first-class subsystem rather than a method stub.
- Diagnostic fingerprint testing is a practical way to measure TypeScript compatibility.
- Solver/checker separation may be a good fit even if `oxc_checker` keeps Oxc as its frontend.
