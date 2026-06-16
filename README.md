# Oxc type checker

This is a proof-of-concept, experimental, do-not-use-in-production type checker based on oxc. This is not an official oxc project.

## Philosophy

The main driver behind this project is to enable an additional layer of information on top of the oxc AST, similar to how `oxc_semantic` layers on top of `oxc_parser` to provide semantic information. This layer would be invaluable for any oxc-based tooling to have type information available for: linting, minification, build tooling, and so on.

This is _not_ a replacement for the TypeScript compiler itself. We will not be focusing on providing a great experience for type checking. Instead, the focus is on resolving types accurately and allowing other programs to utilize that information. That means there's no editor support, no pretty diagnostics printed, just a raw API for type information with basic type checking errors.

## Principles

- Data-oriented: things should be laid out in memory to reduce memory allocations and improve cache efficiency.
- Accurate: we strive to be as accurate and as correct as possible
- Performance-first: simple operations should be fast. as long as it is practical and does not harm correctness, we should choose to be fast in everything.
- Efficient: we should be fast, but not at the expense of memory and resources. we should be able to type check with a minimal amount of memory.

## Goals and non-goals

What we are _not_ doing is almost as important as what we are doing. In order to give this a chance at being maintainable, there are many things that won't be worked on:

| Feature | Status |
| ---- |------- |
| Parsing/scanning | ✅ Implemented with oxc |
| Type resolution and inference | ✅ Mostly works |
| Multi-file analysis | ✅ Mostly works  |
| Programmatic API | 🟠 Core APIs work, but niche APIs (like getting method signature / index access info) are underdeveloped |
| JSX | 📋 Will be supported |
| Project references | 📋 Will be supported |
| JSDoc | ❓ May be supported (not sure yet) |
| Declaration emit | ❌ Not directly supported, but possible to implement with API hopefully |
| Language server (LSP) | ❌ Will not be supported |
| Build mode | ❌ Will not be supported |
| Incremental build | ❌ Will not be supported |
| CLI | ❌ Will not be supported |
| Emit (JS output) | ❌ Will not be supported |
| Watch mode | ❌ Will not be supported |

### Design decisions

- **Always strict mode**: In order to reduce complexity in the type checker, all `strict` configuration options are always enabled, such as `strictNullChecks`.

## FAQ

### How can I contribute?

At the moment, this is not a collaborative project. I'm still rearchitecting huge portions of the checker and accepting external contributions would be incompatible with that.

### What is the performance like?

I'm not currently comparing performance to typescript-go or tsc or any other type checkers at this point, since they support way more functionality and are much more optimized. There is a lot of room for performance improvement still, but I am more focused on making the types accurate right now. There are some simple benchmarks you can run with `cargo bench`.

### Will this be integrated into oxc?

Not something I'm planning right now, but it could be possible in the future.

### Why does this exist?

I think it's possible for a simple type checker to exist independently of `tsc`/`tsgo`. I believe there's value in having multiple implementations of the same type system. I want to learn more about type checking and what it looks like in a practical codebase, so I decided to try implementing it myself.
