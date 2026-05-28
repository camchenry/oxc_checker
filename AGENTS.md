- read the README, it's important
- run `cargo conformance` for full verification
- architecture-wise, aim to be similar to `typescript-go` codebase
- if something should be addressed later, leave a TODO. for example:`TODO(perf)`, `TODO`, `TODO(correctness)`

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

The conformance extractor needs the TypeScript compiler API. Install it into the ignored `target` directory, build the TypeScript submodule so `vendor/TypeScript/built/local/typescript.js` exists, or set `TYPESCRIPT_MODULE=/path/to/typescript.js`.

```sh
npm --prefix target/conformance install typescript
```

Regenerate the TypeScript compiler API record cache and run the default type record comparison with:

```sh
cargo conformance
```

The default conformance run currently covers local custom cases and checked-in external library fixtures. It does not run the upstream TypeScript compiler suite, keeping the normal loop fast while real-world project fixtures are still ramping up.

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

The TypeScript extractor iterates over every `*.ts` and `*.tsx` file in the selected suites: `tests/conformance/cases`, `tests/conformance/external`, and, when explicitly selected, `vendor/TypeScript/tests/cases/compiler`. It writes `target/conformance/cases_tsc_types.tsv` for local cases, `target/conformance/external_tsc_types.tsv` for external library fixtures, and `target/conformance/tsc_types.tsv` for upstream cases. The Rust harness collects matching OXC records in process, compares records by source location and identifier text, and prints compact pass/fail summaries for selected suites.

Each run writes the snapshot for each selected suite: `tests/conformance/cases_snapshot.txt`, `tests/conformance/external_snapshot.txt`, and, when the upstream suite is selected, `tests/conformance/types_snapshot.txt`. These snapshots record every case file, whether it passed or failed, and any errors or mismatches for that file. Local custom cases and external library fixtures also generate sibling `.ts.types` files. Commit those snapshots and `.types` files to track conformance progress over time. External fixtures should include provenance notes with the source repository, commit SHA, copied paths, and any trimming or stubbing performed.
