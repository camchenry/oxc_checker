- read the README, it's important
- run `cargo conformance` for full verification
- architecture-wise, aim to be similar to `typescript-go` codebase

## TypeScript conformance tests

This repository includes a minimal, opt-in conformance harness that compares TypeScript compiler API type records against `oxc_checker` type records for upstream TypeScript compiler cases. The upstream suite is tracked as a git submodule at `vendor/TypeScript`. There are also additional tests under `tests/conformance/cases`.

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

Regenerate the TypeScript compiler API record cache and run the type record comparison with:

```sh
cargo conformance
```

Run a single conformance test file for quick iteration:

```sh
cargo conformance <file path>
```

The TypeScript extractor iterates over every `*.ts` and `*.tsx` file under `vendor/TypeScript/tests/cases/compiler` and `tests/conformance/cases`. It writes `target/conformance/tsc_types.tsv` for upstream cases and `target/conformance/cases_tsc_types.tsv` for local cases. The Rust harness collects matching OXC records in process, compares records by source location and identifier text, and prints compact pass/fail summaries for both suites.

Each run writes `tests/conformance/types_snapshot.txt` and `tests/conformance/cases_snapshot.txt`, which record every case file, whether it passed or failed, and any errors or mismatches for that file. Commit those snapshots to track conformance progress over time.
