---
name: api-guidelines
description: 'Design and review Rust APIs for the type checker. Use when adding new functionality, public items, reusable internal interfaces, constructors, builders, configuration, flags, query methods, or changing an existing API contract.'
argument-hint: 'Describe the API or functionality to design or review'
---

# API Guidelines

Apply these guidelines while designing an API, not only after implementation. They are adapted from the [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) for this type checker's accuracy, performance, arena ownership, and programmatic API goals.

## Scope

- Apply every guideline to public APIs.
- Apply design and type-safety guidelines to reusable internal APIs as well.
- Keep one-off private helpers proportional: clear types and contracts matter, but rustdoc examples are not required.
- Treat API changes as including new types, methods, trait methods, constructors, builders, options, result records, flags, and changes to ownership or failure behavior.

## Workflow

1. Identify the caller, the operation's natural owner, and the data or intermediate results the caller may already have.
2. Sketch the signature and ownership model before implementing it. Account for checker arenas, borrowed AST data, allocation, and repeated queries.
3. Review the sketch against every applicable check below. Resolve failures in the underlying API shape rather than documenting around them.
4. Implement rustdoc with compilable examples for public items. Update crate-level docs when the primary workflow or major capability changes.
5. Add tests for validation and failure behavior. Run focused tests first, then the repository-required verification.

## Documentation

### [Function docs include error, panic, and safety considerations (C-FAILURE)](https://rust-lang.github.io/api-guidelines/documentation.html#function-docs-include-error-panic-and-safety-considerations-c-failure)

- Add `# Errors` when a function returns `Result`, describing the conditions represented by each error category.
- Add `# Panics` when a public function can panic for caller-controlled input or state. Prefer returning an error when invalid external input is expected.
- Add `# Safety` to every `unsafe` API and state all caller obligations needed to avoid undefined behavior.
- Document meaningful sentinel states in `Option` and partial-result records, especially when unresolved or error types can be confused with absence.

### [Crate level docs are thorough and include examples (C-CRATE-DOC)](https://rust-lang.github.io/api-guidelines/documentation.html#crate-level-docs-are-thorough-and-include-examples-c-crate-doc)

- Explain the crate's purpose, core concepts, main entry points, arena and lifetime model, and error-reporting model.
- Include an end-to-end example of the primary parse, check, and query workflow.
- Update crate docs when a new capability changes how consumers construct or query the checker.

### [All items have a rustdoc example (C-EXAMPLE)](https://rust-lang.github.io/api-guidelines/documentation.html#all-items-have-a-rustdoc-example-c-example)

- Add a focused, compiling example to each new public type, trait, function, and non-obvious method.
- Show realistic checker usage and observable behavior, not only construction.
- Use `no_run` only when execution genuinely requires files or expensive setup; do not hide code from compilation merely for convenience.

## Predictability

### [Functions with a clear receiver are methods (C-METHOD)](https://rust-lang.github.io/api-guidelines/predictability.html#functions-with-a-clear-receiver-are-methods-c-method)

Put an operation on the type that owns the relevant state or invariant. Prefer, for example, an arena or checker query method over a free function whose first argument is always that arena or checker. Keep free functions for operations with no natural receiver or for deliberate separation of concerns.

### [Functions do not take out-parameters (C-NO-OUT)](https://rust-lang.github.io/api-guidelines/predictability.html#functions-do-not-take-out-parameters-c-no-out)

Return a value, iterator, or named result record rather than accepting `&mut Option<T>` or several output references. A caller-provided collection may be appropriate only when measured allocation reuse matters; name such APIs explicitly (for example, `collect_*_into`) and also provide an ergonomic returning form when practical.

### [Constructors are static, inherent methods (C-CTOR)](https://rust-lang.github.io/api-guidelines/predictability.html#constructors-are-static-inherent-methods-c-ctor)

Define constructors as `Type::new`, `Type::with_*`, or a domain-specific inherent method. Use `Default` when there is one unsurprising default. Do not introduce a detached `create_type` function when `Type::new` is the natural API.

## Flexibility And Work Avoidance

### [Functions expose intermediate results to avoid duplicate work (C-INTERMEDIATE)](https://rust-lang.github.io/api-guidelines/flexibility.html#functions-expose-intermediate-results-to-avoid-duplicate-work-c-intermediate)

When an operation computes information that callers commonly need, return a result record or query object that retains it rather than forcing duplicate resolution, traversal, relation checks, or allocation. Provide convenience accessors over the rich result. Do not expose unstable implementation details solely to satisfy this rule.

### [Caller decides where to copy and place data (C-CALLER-CONTROL)](https://rust-lang.github.io/api-guidelines/flexibility.html#caller-decides-where-to-copy-and-place-data-c-caller-control)

- Prefer borrowed views, iterators, and arena-backed results over unconditionally cloning into owned collections.
- Accept the caller's allocator, arena, or destination when placement materially affects lifetime or performance.
- Do not return references tied to temporary internal storage or conceal expensive copies behind cheap-looking accessors.

### [Functions minimize assumptions about parameters by using generics (C-GENERIC)](https://rust-lang.github.io/api-guidelines/flexibility.html#functions-minimize-assumptions-about-parameters-by-using-generics-c-generic)

Accept `impl IntoIterator`, `impl AsRef<Path>`, or similarly narrow generic capabilities when they admit useful callers without allocation. Avoid generic abstraction when the checker requires a concrete representation for identity, arena provenance, ordering, or performance; encode those requirements directly.

## Type Safety

### [Newtypes provide static distinctions (C-NEWTYPE)](https://rust-lang.github.io/api-guidelines/type-safety.html#newtypes-provide-static-distinctions-c-newtype)

Use newtypes for identifiers, indexes, handles, offsets, and values that share a primitive representation but are not interchangeable. Preserve provenance where mixing values from different checker arenas or program stores would be incorrect.

### [Arguments convey meaning through types, not `bool` or `Option` (C-CUSTOM-TYPE)](https://rust-lang.github.io/api-guidelines/type-safety.html#arguments-convey-meaning-through-types-not-bool-or-option-c-custom-type)

Replace mode-selecting `bool` parameters with descriptive enums or option types. Avoid ambiguous `Option<T>` parameters when `None` has domain-specific meaning; use a named enum or configuration type. A boolean is acceptable for an intrinsic binary property when its meaning is clear from the field or accessor name.

### [Types for a set of flags are `bitflags`, not enums (C-BITFLAG)](https://rust-lang.github.io/api-guidelines/type-safety.html#types-for-a-set-of-flags-are-bitflags-not-enums-c-bitflag)

Use `bitflags` for independent flags that can be combined. Use an enum for mutually exclusive modes and a struct for heterogeneous configuration. Define and test the behavior of unknown, empty, and combined flag values.

### [Builders enable construction of complex values (C-BUILDER)](https://rust-lang.github.io/api-guidelines/type-safety.html#builders-enable-construction-of-complex-values-c-builder)

Use a builder when construction has many optional settings, staged inputs, or invariants that should be validated once. Keep required inputs in `new` when possible, make option methods chainable, and perform final validation in `build`. Do not add a builder for a small value with an obvious constructor.

## Dependability And Evolution

### [Functions validate their arguments (C-VALIDATE)](https://rust-lang.github.io/api-guidelines/dependability.html#functions-validate-their-arguments-c-validate)

Reject invalid paths, IDs, arena provenance, option combinations, and lifecycle transitions before mutating shared state or starting expensive work. Return structured errors for expected invalid input; reserve assertions for internal invariants that callers cannot violate through the safe API.

### [Structs have private fields (C-STRUCT-PRIVATE)](https://rust-lang.github.io/api-guidelines/future-proofing.html#structs-have-private-fields-c-struct-private)

Use constructors and accessors to preserve invariants and future flexibility. Expose fields only for deliberately transparent, stable data records where direct construction and exhaustive access are part of the contract; consider `#[non_exhaustive]` when fields may grow.

### [Newtypes encapsulate implementation details (C-NEWTYPE-HIDE)](https://rust-lang.github.io/api-guidelines/future-proofing.html#newtypes-encapsulate-implementation-details-c-newtype-hide)

Keep newtype fields private when the representation or valid range is an implementation detail. Expose checked constructors and narrow accessors instead of allowing arbitrary primitive values.

### [Data structures do not duplicate derived trait bounds (C-STRUCT-BOUNDS)](https://rust-lang.github.io/api-guidelines/future-proofing.html#data-structures-do-not-duplicate-derived-trait-bounds-c-struct-bounds)

Do not put trait bounds on a struct or enum solely because a derived implementation needs them. Put bounds on the relevant `impl` blocks so the data type remains usable with the broadest valid set of parameters.

## Review Output

When reviewing an API, report applicable guideline IDs, the concrete caller impact, and a specific signature or design change. If a guideline is intentionally not followed, record the performance, correctness, or compatibility reason in the review or nearby API documentation.