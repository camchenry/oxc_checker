- read the README, it's important
- run `cargo conformance` for full verification after making any changes
- architecture-wise, aim to be similar to `typescript-go` codebase and use that as a reference for correctness
- if something should be addressed later, leave a TODO. for example:`TODO(perf)`, `TODO`, `TODO(correctness)`
- don't hard-code things or overfit to the test data. do the more general and more correct method always, unless it's for performance.
- don't just check global types by name, we have to take into account that types like `Record`, could just be named that by the user.

## TypeScript conformance tests

This repository includes a minimal, opt-in conformance harness that compares TypeScript compiler API type records against `oxc_checker` type records for upstream TypeScript compiler cases. The upstream suite is tracked as a git submodule at `vendor/TypeScript`. There are also additional tests under `tests/conformance/cases` and checked-in trimmed external library fixtures under `tests/conformance/external`.

Initialize the submodule before running the conformance test:

```sh
git submodule update --init vendor/TypeScript
```

The normal test suite does not run the TypeScript conformance harness:

```sh
cargo test
```

The conformance extractor needs the TypeScript compiler API. Install the checked-in conformance npm dev dependencies, build the TypeScript submodule so `vendor/TypeScript/built/local/typescript.js` exists, or set `TYPESCRIPT_MODULE=/path/to/typescript.js`.

```sh
npm --prefix tests/conformance install
```

Run the default type record comparison with the checked-in TypeScript compiler API record cache:

```sh
cargo conformance
```

Regenerate the checked-in TypeScript compiler API record cache and then run the selected comparison with:

```sh
cargo conformance-refresh
```

Use the refresh command when TypeScript extractor behavior, compiler options, fixtures, or the TypeScript compiler version change. The default conformance command intentionally skips Node/TypeScript extraction and only runs the Rust checker against stored records.

The default conformance run currently covers local custom cases and checked-in external library fixtures. It does not run the upstream TypeScript compiler suite, keeping the normal loop fast while real-world project fixtures are still ramping up.

Run every suite, including the upstream TypeScript compiler suite, with:

```sh
cargo conformance full
```

Run only the checked-in external library fixture suite with:

```sh
cargo conformance external
```

Run only the upstream TypeScript compiler suite with:

```sh
cargo conformance typescript
```

The upstream TypeScript compiler suite takes like 7-8 minutes to run currently.

Run a single conformance test file for quick iteration:

```sh
cargo conformance <file path>
```

The TypeScript extractor iterates over every `*.ts` and `*.tsx` file in the selected suites: `tests/conformance/cases`, `tests/conformance/external`, `src/lib`, and, when explicitly selected, `vendor/TypeScript/tests/cases/compiler`. It writes checked-in TSV caches under `tests/conformance/tsc-types`. The Rust harness collects matching OXC records in process, compares records by source location and identifier text, and prints compact pass/fail summaries for selected suites.

Each run writes the snapshot for each selected suite: `tests/conformance/cases_snapshot.txt`, `tests/conformance/external_snapshot.txt`, `tests/conformance/lib_snapshot.txt`, and, when the upstream suite is selected, `tests/conformance/types_snapshot.txt`. These snapshots record every case file, whether it passed or failed, and any errors or mismatches for that file. Local custom cases, external library fixtures, and standard library declarations also generate `.ts.types` files. Commit those snapshots, `.types` files, and `tests/conformance/tsc-types/*.tsv` files to track conformance progress over time. External fixtures should include provenance notes with the source repository, commit SHA, copied paths, and any trimming or stubbing performed.
