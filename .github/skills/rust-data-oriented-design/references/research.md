# Research Notes

These notes distinguish stable language contracts from implementation observations and optimization advice. Sources were reviewed on 2026-08-18.

## Normative Rust layout sources

- [Rust Reference: Type layout](https://doc.rust-lang.org/reference/type-layout.html): size includes array stride padding; alignment is target-specific; `repr(Rust)` guarantees alignment and non-overlap but not declaration order; `repr(C)` specifies declaration-order struct layout; `repr(packed)` can make fields unaligned; `repr(transparent)` delegates layout and ABI to its non-zero-sized field.
- [Rust standard library: `size_of`](https://doc.rust-lang.org/std/mem/fn.size_of.html): measures byte stride between array elements. Type size is generally not stable across compilations. The documentation lists guaranteed pointer-sized `Option<&T>` and `Option<Box<T>>` cases.
- [Rust standard library: `offset_of!`](https://doc.rust-lang.org/std/mem/macro.offset_of.html): observes field offsets, while warning that default layout is platform-specific and can change between compilations.
- [Rust standard library: `Layout`](https://doc.rust-lang.org/std/alloc/struct.Layout.html): models size, power-of-two alignment, padding, extension, and array stride. It cannot reproduce unspecified `repr(Rust)` field layout.
- [Rustonomicon: `repr(Rust)`](https://doc.rust-lang.org/nomicon/repr-rust.html): explains padding, field reordering freedom, and enum niche optimization. Use the Reference rather than the Nomicon as the final authority when they differ.

Implications:

- Measure concrete monomorphized types on every supported target that matters.
- Treat compiler-selected field order and undocumented enum niches as observations, not contracts.
- Prefer default representation for internal Rust types unless FFI, serialization-by-layout, or unsafe code requires a stable representation.
- Never infer safe transmutation from equal size and alignment alone.

## Rust performance guidance

- [Rust Performance Book: Type sizes](https://nnethercote.github.io/perf-book/type-sizes.html): use `-Zprint-type-sizes`; shrink frequently instantiated types; inspect outsized enum variants; narrower integers, boxed cold variants, and boxed slices can reduce parent size but have tradeoffs; target-gate size assertions.
- [Rust Performance Book: Heap allocations](https://nnethercote.github.io/perf-book/heap-allocations.html): profile allocation sites; reserve from observed lengths; inline vectors reduce allocation but can enlarge every container and add a branch; reuse collections where repeated allocation is hot.
- [Rust Performance Book: Profiling](https://nnethercote.github.io/perf-book/profiling.html): optimize code shown to be hot by a suitable profiler. It lists platform tools including Instruments, samply, flamegraph, Cachegrind, DHAT, and heap profilers.
- [Criterion.rs book](https://bheisler.github.io/criterion.rs/book/): Criterion collects statistical benchmark data and compares runs, but benchmark validity still depends on a representative workload and correct timed boundaries.
- [Rust standard library: `black_box`](https://doc.rust-lang.org/std/hint/fn.black_box.html): useful for benchmarks on a best-effort basis; it cannot guarantee that all unwanted optimization is blocked and must not be used for program correctness.

## Cache and hardware guidance

- [Linux CPU cache sysfs ABI](https://www.kernel.org/doc/Documentation/ABI/testing/sysfs-devices-system-cpu): exposes cache level, type, size, associativity, sharing, and `coherency_line_size`. This is direct evidence that line properties belong to the target rather than the Rust language.
- [Intel architecture and optimization manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html): provide microarchitecture-specific cache, prefetch, memory, and performance-counter guidance. Apply only to the processor families covered by the relevant manual.

Implications:

- "Fits in 64 bytes" is a target-specific observation, not a portable Rust invariant.
- A cache line is a transfer/coherency unit, not a natural Rust object boundary. Values can straddle lines and share lines with neighbors.
- Spatial locality, working-set size, access order, and useful-byte density usually matter before explicit alignment.
- Padding can mitigate measured false sharing but increases stride and total footprint; validate both throughput and memory effects.

## Repository-specific evidence

- [Checker performance harness](../../../../docs/profiling.md) separates program construction, planning, and checking; records raw iterations; reports system allocation, arena growth, RSS, and timing distributions; and documents release profiling with samply, flamegraph, and Instruments.
- Existing repository measurements show that compact arena tails, inline small collections selected from observed cardinalities, dense bitsets for dense IDs, and work avoidance can improve memory and CPU together. These are examples, not universal rules; repeat the workload-specific experiment for each proposed use.