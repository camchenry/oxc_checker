read the README, it's important

## TypeScript conformance tests

This repository includes a minimal, opt-in conformance harness that compares TypeScript compiler API type records against `oxc_checker` type records for upstream TypeScript compiler cases. The upstream suite is tracked as a git submodule at `vendor/TypeScript`.

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

Regenerate the TypeScript compiler API record cache explicitly with:

```sh
cargo conformance-tsc
```

Run the compiler-case type record comparison with:

```sh
cargo conformance
```

The TypeScript extractor iterates over every `*.ts` and `*.tsx` file under `vendor/TypeScript/tests/cases/compiler` and writes `target/conformance/tsc_types.tsv`. The Rust harness reuses that cached file, writes `target/conformance/oxc_types.tsv`, compares the two files by source location and identifier text, and prints a compact pass/fail summary.

Each run writes `tests/conformance/types_snapshot.txt`, which records every compiler case file, whether it passed or failed, and any errors or mismatches for that file. Commit that snapshot to track conformance progress over time.
