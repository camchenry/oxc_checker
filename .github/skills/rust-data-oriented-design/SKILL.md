---
name: rust-data-oriented-design
description: 'Design, implement, and review data-oriented Rust code using measured memory layout and access patterns. Use for struct or enum sizing, cache locality, cache lines, hot/cold splitting, AoS versus SoA, compact IDs, arenas, allocation reduction, pointer chasing, false sharing, and memory-footprint performance work.'
argument-hint: 'Describe the Rust data structure, workload, or locality problem'
---

# Rust Data-Oriented Design

Optimize the shape and movement of data for a demonstrated workload. Treat type size, cache behavior, and allocation count as explanatory metrics, not goals by themselves. Preserve correctness and API clarity unless evidence justifies a tradeoff.

Read [the research notes](./references/research.md) when making claims about Rust layout guarantees, representation attributes, cache-line sizes, or measurement tools.

## Required Workflow

### 1. Define the workload

Before proposing a representation, record:

- The user-visible goal: latency, throughput, peak memory, retained memory, or allocation traffic.
- The representative input sizes, data distributions, target architectures, and concurrency.
- The hot operation and phase. Separate construction, mutation, traversal, lookup, and destruction.
- A correctness guardrail and a practical improvement threshold.
- A falsifiable hypothesis connecting one observed cost to one proposed layout change.

Do not infer hotness from a large type alone. Profile first when no trustworthy workload evidence exists.

### 2. Map access and lifetime

For each candidate field or collection, determine:

- How many instances are live and how often each field is read or written.
- Which fields are accessed together in the hot path.
- Whether traversal is sequential, random, sparse, or keyed.
- Typical and tail cardinalities, not only maximum cardinality.
- Which data is immutable, append-only, temporary, or long-lived.
- Whether threads write neighboring values or share ownership.

Estimate total footprint as `size_of::<T>() * live_count`, then include collection capacity, allocator overhead, side allocations, and pointed-to data. A smaller handle that adds a random pointer chase may be slower than a larger contiguous value.

### 3. Inspect the actual layout

Use the exact release target and representative feature set whenever possible.

```rust
use std::mem::{align_of, offset_of, size_of};

println!("size={} align={}", size_of::<HotType>(), align_of::<HotType>());
println!("field_offset={}", offset_of!(HotType, field));
```

For detailed compiler output, use nightly on a focused target:

```sh
RUSTFLAGS=-Zprint-type-sizes cargo +nightly build --release
```

Record at least:

- Type size, alignment, field offsets, and padding.
- Enum discriminant, largest variant, and variant frequency.
- Pointer-sized fields and their transitive allocations.
- Container length and capacity distributions.
- Instance count and total bytes attributable to the representation.

Treat default `repr(Rust)` layout as an observation for this compiler and target, not a stable contract. Rust may reorder fields. Use `#[repr(C)]` only when declaration-order layout or ABI interoperability is required; it is not a general size optimization.

### 4. Choose the representation from the access pattern

Prefer changes in this order:

1. Eliminate work, improve the algorithm, or avoid storing derivable data.
2. Keep hot traversals contiguous and reduce indirection.
3. Reduce per-element footprint and unnecessary data movement.
4. Reduce allocation count and wasted capacity.
5. Tune alignment, cache-line placement, or prefetch behavior only with target-specific evidence.

#### Array of structs

Use `Vec<Record>` or slices when most fields are consumed together, records are naturally iterated as units, or per-record operations dominate. It keeps invariants local and is usually the simplest baseline.

#### Struct of arrays

Use parallel `Vec<Field>` columns when hot passes touch only a small subset of fields across many records and the saved bandwidth is material. Encapsulate columns behind one owner, keep lengths synchronized, and use typed indices. Account for more allocations, more complex mutation, and reconstruction costs.

Use an array-of-structs-of-arrays layout only when measured batching or vectorization benefits justify the added complexity.

#### Hot/cold splitting

Move large or rarely accessed fields out of a densely scanned record when most operations need only the hot prefix. Choose storage based on lifecycle:

- A parallel side table or arena can preserve dense ownership and amortize allocation.
- `Box<Cold>` shrinks the parent but adds an allocation and pointer chase.
- An optional index or handle can be smaller than an optional pointer, but must validate range and provenance.

Do not move a field out merely because it is semantically "cold". Confirm its access frequency and the resulting parent size.

#### Enums and optional data

- Measure the discriminant, niche use, largest variant, and real variant distribution.
- Box or side-store an outsized rare variant only when the common-case density gain outweighs allocation and indirection.
- Prefer `Option<NonZero*>`, references, or other niche-capable types only when their domain semantics are correct. Verify size rather than assuming niche optimization.
- An explicit `#[repr(u8)]` changes the representation contract and may prevent compiler optimizations. Use it for a required contract, not as a speculative shrink.

#### Compact scalars and handles

- Use the narrowest integer that represents the proven domain, with checked construction and conversion.
- Prefer typed IDs or indices over pointers when data lives in stable contiguous storage.
- Include generation or provenance when stale or cross-arena handles are possible.
- Pack independent booleans into flags when footprint matters, but avoid manual bit packing that makes hot updates or reads more expensive without evidence.

#### Collections and allocation

- Reserve from observed cardinalities when growth reallocations are significant.
- Freeze immutable vectors into slices when capacity and mutation are no longer needed.
- Use inline storage only when the measured length distribution makes the inline capacity effective. Include the larger container size and spill branch in the comparison.
- Prefer dense vectors or bitsets over hash tables when keys are dense IDs and ordering semantics allow it.
- Reuse scratch buffers when profiles show repeated temporary allocation and ownership remains clear.
- Use arenas when many values share a lifetime and bulk reclamation fits the domain. Account for retained capacity and destructor needs.

### 5. Structure hot code around the data

- Iterate contiguous slices directly and keep the hot loop focused on fields it actually needs.
- Batch by kind or phase when it removes repeated dispatch or unpredictable branching without duplicating excessive state.
- Avoid linked structures, trait-object dispatch, hash lookup, and nested heap ownership in hot traversal unless their semantics are necessary.
- Reuse computed indices, classifications, and intermediate results when doing so avoids repeated traversal and does not inflate every record.
- Consider fusing passes that consume the same data, and splitting passes that touch disjoint columns. Benchmark both; either can win depending on working set and branch behavior.
- Keep cold error handling and formatting out of the common path where practical, without changing observable behavior.

### 6. Treat cache lines as target properties

Do not assume every target has a 64-byte cache or coherency line. Discover the deployment target's properties or state the target-specific assumption. On Linux, `coherency_line_size` is exposed under `/sys/devices/system/cpu/cpu*/cache/index*/`.

A type being smaller than one cache line does not mean each value occupies one line: allocation alignment, array stride, neighboring data, and boundary crossings matter. Optimize useful bytes per traversal before trying to align individual objects.

For concurrent mutation:

- Partition ownership so threads write disjoint regions first.
- Suspect false sharing only when profiles or scaling behavior implicate coherency traffic.
- Apply cache-line padding or `#[repr(align(N))]` only to the contended state and only for known targets.
- Measure the increased footprint and cache pressure. Over-alignment can make arrays dramatically larger.

### 7. Avoid representation traps

- Do not use `#[repr(packed)]` as a routine size optimization. It creates unaligned fields, restricts references, and can make access slower or unsafe.
- Do not add `unsafe` solely to remove bounds checks or express a custom layout until profiles identify the cost and a safe representation cannot solve it.
- Do not rely on field offsets, enum layout, or niche behavior across compilations unless Rust documents the guarantee or an explicit representation supplies it.
- Do not optimize only `size_of::<T>()`. Include allocations, capacity, live count, memory traffic, and end-to-end behavior.
- Do not assume fewer cache misses means faster code; hardware counters help explain a measured result but do not replace it.

### 8. Validate the change

1. Run focused correctness tests before and after the change.
2. Compare optimized builds with identical inputs, features, toolchain, target, and instrumentation.
3. Interleave baseline and candidate runs or use multiple independent processes when differences are small.
4. Compare end-to-end time plus relevant guardrails: allocations, allocated bytes, retained bytes, peak RSS, type count, and output identity.
5. Inspect cache-miss, branch, or coherency counters only when they test the stated mechanism.
6. Test typical and tail sizes so an inline or compact representation does not merely move the crossover point.
7. Add a target-gated size assertion or stable benchmark only for an important regression risk.

Use `std::hint::black_box` in microbenchmarks to inhibit irrelevant optimization, but remember that it is best-effort and does not make an unrealistic workload representative.

For this repository, use the harness in [docs/profiling.md](../../../docs/profiling.md) for CPU, allocation, arena, and memory comparisons. Run a focused check first and `cargo conformance` after checker changes, as required by `AGENTS.md`.

## Review Output

Report:

- Workload, target, baseline, and falsifiable hypothesis.
- Before/after type layout and total-footprint estimates.
- Access-pattern reasoning for the chosen representation.
- Correctness, ownership, API, portability, and complexity tradeoffs.
- Before/after measurements with raw command/configuration and uncertainty.
- Whether results support, falsify, or leave the hypothesis inconclusive.

Reject changes justified only by intuition, a debug-build result, one timing sample, or an unverified cache-line claim.