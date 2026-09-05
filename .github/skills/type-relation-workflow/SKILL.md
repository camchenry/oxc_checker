---
name: type-relation-workflow
description: 'Implement, fix, debug, or review type relations in oxc_checker. Use for assignability, identity, comparability, subtyping, union or intersection relations, type reduction, apparent types, generic signature compatibility, and conformance relation mismatches.'
argument-hint: 'Describe the relation mismatch or proposed semantic change'
---

# Type Relation Workflow

Use this workflow for every change to assignability or related type relations. The reported example is evidence for a rule, not the rule itself.

## 1. Validate and minimize the example

1. Reduce the failure to the smallest source and target types that preserve it.
2. Confirm the expected direction: `source` assignable to `target` is not interchangeable with the reverse.
3. Run the smallest relevant conformance fixture and inspect both the printed types and their kinds.
4. Distinguish a relation failure from incorrect type construction, reduction, printing, or fixture expectations before editing relation code.

## 2. State the general semantic rule

Before changing code, write down:

- the source and target type families covered by the rule;
- whether constituent quantification is `all` or `some` in each direction;
- required normalization, reduction, apparent-type conversion, or contextual instantiation;
- identity, `never`, `any`, `unknown`, literal, and generic boundary behavior that applies;
- where the rule naturally belongs: type construction, shared reduction/materialization, apparent-type resolution, or relation dispatch.

Check adjacent type kinds and the reverse direction. Do not derive a branch solely from one concrete pair of types.

## 3. Use TypeScript-Go as the oracle

Search the `typescript` workspace, especially `tsc/internal/checker/relater.go` and nearby checker helpers. Trace the complete control flow rather than copying one condition: prerequisite normalization and later fallback checks may be semantically essential.

Record:

- the corresponding tsgo entry point and branch;
- helpers called before and after it;
- relation state, recursion guards, caches, and flags involved;
- any representation difference that requires adapting rather than transliterating the implementation.

If behavior intentionally differs from tsgo, state that explicitly before implementation.

## 4. Build a compact semantic matrix

Add positive and negative cases for the applicable dimensions:

- assignment direction;
- direct type versus alias/reference;
- literal versus widened primitive;
- object, primitive, union, and intersection neighbors;
- generic versus instantiated form;
- reducible versus irreducible form;
- structurally equal but non-identical types;
- special types such as `never`, when relevant.

Prefer adding cases to an existing file under `tests/conformance/cases/compiler`. Create a focused conformance file when no existing fixture has a clear semantic home. Prefer conformance fixtures over equivalent Rust-only tests to keep compile times lower and compare directly with TypeScript.

Run the focused fixture before implementation and confirm it demonstrates the missing behavior.

## 5. Implement at the owning layer

Prefer shared normalization, reduction, materialization, or relation machinery over source/target-kind special cases. Reuse a semantic intermediate result when multiple consumers need the same resolution. Preserve recursion guards and relation caches; relation correctness includes termination.

If the implementation needs a new reusable API, also apply the `api-guidelines` skill. If representation or layout changes are involved, apply the `rust-data-oriented-design` skill.

## 6. Validate

Run in this order:

1. the focused conformance fixture;
2. closely related fixtures when the rule spans multiple forms;
3. `cargo test` and `cargo lint` when Rust code changed;
4. `cargo conformance full` after any checker behavior change.

The full conformance run currently takes less than 30 seconds. Review all changed mismatches by semantic category; do not accept broad snapshot movement merely because the focused case passes.

When a fixture becomes unexpectedly slow or hangs, stop broad retries and apply the `checker-performance-diagnostics` skill.
