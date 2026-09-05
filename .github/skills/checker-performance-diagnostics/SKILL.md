---
name: checker-performance-diagnostics
description: 'Diagnose slow or hanging oxc_checker tests and conformance fixtures. Use when cargo test or cargo conformance stalls, times out, regresses in runtime, loops in type relations, or needs CPU, memory, allocation, or phase profiling.'
argument-hint: 'Provide the slow test, conformance fixture, or command'
---

# Checker Performance Diagnostics

Diagnose first; do not repeatedly rerun a broad suite without collecting evidence. Separate compilation time from execution time and preserve a stack sample when execution exceeds the expected bound.

## Fast hang workflow

1. Identify the narrowest command that reproduces the problem.
2. Build it without a diagnostic timeout so compilation is not mistaken for checker execution:
   - conformance: `cargo test --features conformance --no-run`;
   - a Rust test: `cargo test --no-run`.
3. Build the standalone diagnostic tool once:
   - `rustc --edition 2024 .github/skills/checker-performance-diagnostics/scripts/diagnose_hang.rs -o target/diagnose_hang`
4. Run the already-built command through [diagnose_hang.rs](./scripts/diagnose_hang.rs). For example:
   - `target/diagnose_hang --timeout 20 --conformance-timing -- cargo conformance path/to/case.ts`
   - `target/diagnose_hang --timeout 20 -- cargo test test_name -- --exact --nocapture`
5. If the deadline is exceeded, inspect the generated process list, combined output log, and macOS stack samples under `target/hang-diagnostics/`.
6. Re-run the narrow reproducer once to establish whether the same stack and phase recur. Do not classify an interrupted build, stale terminal notification, or snapshot generation as a deterministic checker hang.

The diagnostic tool owns its execution deadline and process cleanup. Do not wrap normal builds or routine test runs in an external `timeout` command.

## Interpret conformance timing

`--conformance-timing` sets `OXC_CONFORMANCE_TIMING=1`. Use the emitted collection timing to distinguish:

- file reading or fixture discovery;
- channel backpressure (`send_wait`);
- aggregate checker work (`check_sum`);
- wall-clock parallel execution.

Build first: otherwise command wall time includes compilation and does not measure the fixture.

## Isolate checker phases

For a real TypeScript root file, use `profile_checker` when conformance timing is insufficient. It reports program build, query planning, and repeated checker passes separately:

1. Build once with `cargo build --profile release-with-debug --features bench --bin profile_checker`.
2. Run `target/release-with-debug/profile_checker --warmup 0 --iterations 1 path/to/root.ts` for cold behavior.
3. Use warmups and repeated iterations for stable CPU measurements.
4. Add `--json target/report.json` to preserve evidence.

Consult [the profiling guide](../../../docs/profiling.md) for allocation tracking, `samply`, flamegraphs, Instruments, and interpretation. Use the `performance-thinking` skill for before/after performance claims.

## Relation-loop diagnosis

When stacks remain in assignability, reduction, apparent-type, inference, or property resolution:

1. Identify the repeating source/target pair or type-resolution operation.
2. Determine whether recursion changes semantic state or only allocates a fresh representation.
3. Compare recursion guards and relation caches with tsgo.
4. Check whether normalization occurs before cache lookup and therefore prevents stable identity.
5. Add a minimized conformance fixture that terminates in TypeScript.
6. Fix the shared termination invariant, not only the fixture's named type combination.

## Completion criteria

A hang fix is complete only when:

- the narrow reproducer completes repeatedly;
- the captured hot/repeating stack is no longer present;
- focused semantic output remains correct;
- `cargo conformance full` completes (currently less than 30 seconds);
- `cargo test` and `cargo lint` pass for Rust changes.
