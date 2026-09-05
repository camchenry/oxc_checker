---
name: typescript-conformance-tests
description: 'Run, refresh, debug, and review the oxc_checker TypeScript conformance harness. Use when changing checker behavior, working with conformance cases, snapshots, type records, external fixtures, the TypeScript nightly extractor, or deciding which conformance command and generated outputs are required.'
argument-hint: 'Describe the checker change or conformance test task'
---

# TypeScript Conformance Tests

Use the conformance harness to compare TypeScript nightly API type records against `oxc_checker` type records. The upstream TypeScript compiler suite is tracked as a git submodule at `vendor/TypeScript`. Additional tests live under `tests/conformance/cases`, and checked-in trimmed external library fixtures live under `tests/conformance/external`.

## Required verification

Run `cargo conformance full` after making checker changes. This full verification can be skipped for changes limited to documentation, tests, or other work that cannot affect checker behavior.

The full upstream suite currently takes approximately 7–8 minutes. During development, run the narrowest relevant command first, then run the required full verification at the end.

## Setup

Initialize the upstream TypeScript submodule before running the upstream suite:

```sh
git submodule update --init vendor/TypeScript
```

The normal Rust test suite does not run the TypeScript conformance harness:

```sh
cargo test
```

The conformance extractor uses the unstable synchronous API from the exact TypeScript nightly pinned in `tests/conformance/package.json`. Install the checked-in conformance npm development dependencies before refreshing records:

```sh
npm --prefix tests/conformance install
```

## Commands

Run the default type-record comparison using the checked-in TypeScript nightly API record cache:

```sh
cargo conformance
```

The default run covers local custom cases, checked-in external library fixtures, and standard library declarations. It intentionally skips Node/TypeScript extraction and the upstream TypeScript compiler suite.

Regenerate the checked-in TypeScript nightly API record cache, then run the selected comparison:

```sh
cargo conformance-refresh
```

Refresh records when extractor behavior, compiler options, fixtures, or the pinned TypeScript compiler version changes.

Run every suite, including the upstream TypeScript compiler suite:

```sh
cargo conformance full
```

Run only the checked-in external library fixture suite:

```sh
cargo conformance external
```

Run only the upstream TypeScript compiler suite:

```sh
cargo conformance typescript
```

Run one conformance test file for quick iteration:

```sh
cargo conformance <file path>
```

## Records and outputs

The TypeScript extractor visits every `*.ts` and `*.tsx` file in the selected suites:

- `tests/conformance/cases`
- `tests/conformance/external`
- `src/lib`
- `vendor/TypeScript/tests/cases/compiler` when the upstream suite is explicitly selected

It writes checked-in TypeScript record caches under `tests/conformance/tsc-types`. The Rust harness collects matching OXC records in process, compares records by source location and identifier text, and prints compact pass/fail summaries for the selected suites.

Each run writes the snapshot for every selected suite:

- `tests/conformance/cases_snapshot.txt`
- `tests/conformance/external_snapshot.txt`
- `tests/conformance/lib_snapshot.txt`
- `tests/conformance/types_snapshot.txt` when the upstream suite is selected

Snapshots record every case file, whether it passed or failed, and any errors or mismatches. Local custom cases, external library fixtures, and standard library declarations also generate human-readable `.ts.types` files and machine-readable `.ts.types.jsonl` files.

Commit the snapshots, generated type outputs, and `tests/conformance/tsc-types/*.jsonl` records needed to track the conformance change. External fixtures must include provenance notes with the source repository, commit SHA, copied paths, and any trimming or stubbing performed.
