[ai slop]

# Checker performance harness

`profile_checker` loads a real project from one or more TypeScript root files, follows transitive
imports through `FsProgramHost`, builds reusable query plans for every non-library source file, and
runs the same checker workload repeatedly. It reports program construction separately from checker
execution so CPU profiles can focus on either part.

## Baseline run

Always measure an optimized build. Debug builds are useful for debugging but not comparisons.

```sh
cargo run --release --bin profile_checker -- \
  --warmup 5 --iterations 30 --json target/profile-baseline.json \
  /path/to/project/src/index.ts
```

The terminal report includes:

- source/library file counts, source bytes, semantic nodes, and planned checker queries;
- wall time, user CPU time, system CPU time, and effective CPU utilization;
- arena byte growth for build, planning, and every checker pass;
- system allocator calls, allocated/deallocated bytes, and net live-byte change;
- process peak resident set size (RSS);
- min, mean, median, p95, max, and standard deviation across measured passes.

The unmeasured `census` line runs the same check workload once and groups registered checker types by
kind. Use its largest families to identify which type constructors dominate retained arena storage.

### Phases

**Build** creates the `ProgramStore`. It reads the root files, resolves and reads their transitive
imports, parses every source file, builds semantic and control-flow data, loads the selected embedded
standard libraries, and constructs the program-wide global symbol table. This is the cold front-end
cost; it does not run checker type queries.

**Planning** walks the semantic nodes in every non-library file and records the locations that the
harness will query, such as identifiers, properties, parameters, member expressions, and type alias
declarations. It makes every check pass execute the same workload. Planning does not resolve types,
and standard-library files are not added to the query plan.

**Check** builds a checker for each source-file plan and runs the recorded type-at-location and type
alias queries against the already-built `ProgramStore`. It can consult standard-library and imported
types, but excludes file I/O, parsing, semantic analysis, planning, diagnostics formatting, and type
string rendering. Warmup passes run the same check workload before timing; each reported `check N`
line is one complete measured pass over all plans.

The JSON report retains every raw iteration and uses `schema_version` for future tooling. Keep the
input commit, Rust toolchain, command, machine power mode, and report together when comparing runs.
Close noisy applications and run several independent processes when a change is within a few percent.

The harness wraps Rust's system allocator and always counts process-wide allocation, reallocation,
and deallocation requests. `system.allocated_bytes` measures total heap traffic during a phase,
including memory freed before the phase ends. `system.live_bytes_delta` measures retained heap bytes;
a positive per-check value can reveal data moved out of the arena into ordinary collections.

System allocated bytes include backing chunks requested by the arena. They cannot be directly
subtracted from `arena_bytes_delta`: arena bytes measure occupied bump storage, while system bytes
measure allocator requests and include unused chunk capacity. Compare both trends across otherwise
identical runs. An occasional large positive system live delta can be an arena chunk-capacity growth
event, especially when many checker passes share one allocator; check whether later passes reuse that
capacity before attributing the spike to an off-arena cache. Repeated positive live deltas without
corresponding arena growth are stronger evidence of off-arena retention. `peak_live_bytes` is the
tracked allocator's process-lifetime high-water mark; RSS also includes code, mapped files, allocator
metadata, and other memory outside this wrapper.

Arena allocation/reallocation call counts require OXC allocator instrumentation:

```sh
cargo run --release --features allocation-stats --bin profile_checker -- \
  --iterations 10 --json target/profile-allocations.json \
  /path/to/project/src/index.ts
```

`arena_bytes_delta` is retained arena growth, not total temporary allocation traffic. Peak RSS is a
process lifetime high-water mark, so it does not decrease between phases. Both the system wrapper's
atomic counters and OXC allocation tracking add overhead; compare timing results only between runs
with the same instrumentation.

Use `--no-default-lib` to isolate a declaration file or `--lib-target es2022` to control the embedded
standard libraries. Multiple positional roots are accepted and deduplicated by `ProgramStore`.

## CPU profiles

Build once with release optimizations and debug symbols:

```sh
cargo build --profile release-with-debug --bin profile_checker
```

Generate an interactive Firefox Profiler capture with `samply`:

```sh
samply record target/release-with-debug/profile_checker \
  --warmup 5 --iterations 100 /path/to/project/src/index.ts
```

Generate a flamegraph (macOS may request elevated profiling permissions):

```sh
cargo flamegraph --profile release-with-debug --bin profile_checker -- \
  --warmup 5 --iterations 100 /path/to/project/src/index.ts
```

For Instruments, start the harness with `--pause-before-check`, attach Time Profiler to the printed
PID, start recording, and press Enter. This excludes parsing, semantic construction, planning, and
warmup from the captured interval. Without the pause, a process launch profile includes setup costs.

## Memory profiles

Use Instruments Allocations or Leaks with `--pause-before-check` to focus on checker allocations.
For whole-process peak memory on macOS, wrap a one-iteration cold run:

```sh
/usr/bin/time -l target/release-with-debug/profile_checker \
  --warmup 0 --iterations 1 /path/to/project/src/index.ts
```

The harness intentionally reuses one store across checker passes. Per-pass arena growth reveals
retained checker data and cache behavior, while the first measured pass is closest to cold checker
cost. Use `--warmup 0 --iterations 1` in fresh processes for cold-memory comparisons; use warmups and
many iterations for steady-state CPU comparisons.

## Interpreting results

- Compare the same `checker_queries` count. A query-count change means the workload changed.
- High wall time with lower CPU time usually means scheduling, page faults, or I/O during setup.
- CPU utilization above 100% indicates work occurred on multiple cores.
- A rising per-pass arena delta indicates checker-owned data is retained on repeated construction.
- Stable arena use with rising RSS can come from allocator capacity, non-arena allocations, or profiler overhead.
- Treat p95 as noise-sensitive. Median is usually the better before/after headline; retain raw samples.
