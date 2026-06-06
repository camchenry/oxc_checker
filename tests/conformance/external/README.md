# External Conformance Fixtures

This directory contains checked-in, trimmed TypeScript fixtures based on popular libraries. The fixtures are small compiler-style programs that use `// @filename:` blocks so the TypeScript extractor and OXC fixture host resolve the same virtual files.

## TanStack Query

- Repository: https://github.com/TanStack/query
- Commit: d5630c939fb9726382ed000bab7cd7a119c7173c
- License: MIT
- Fixture: `tanstack-query/query-core-streamed-query.ts`
- Source paths:
  - `packages/query-core/src/types.ts`
  - `packages/query-core/src/streamedQuery.ts`
- Curation notes: copied the query-key, data-tag, query-function-context, infinite-data, and streamed-query type shapes that exercise conditional types, indexed access, generic function returns, and stream reducer inference. Runtime cache behavior and unrelated query-core dependencies are replaced with small local stubs.

## ts-toolbelt

- Repository: https://github.com/millsp/ts-toolbelt
- Commit: b8a49285e3ed3a7d8bb8e0b433389eac46a5f140
- License: Apache-2.0
- Fixture: `ts-toolbelt/object-optional.ts`
- Source paths:
  - `sources/Object/Optional.ts`
  - `sources/Any/Equals.ts`
  - minimal supporting shapes from `sources/Any/Key.ts`, `sources/Object/_Internal.ts`, `sources/Object/Pick.ts`, and `sources/Object/Patch.ts`
- Curation notes: copied the optional-object utility type shape and equality helper, with compact local versions of supporting aliases so the fixture remains reviewable while still exercising mapped types, conditional type selection, default generic parameters, and deep recursive object transforms.

## Type-Fest

- Repository: https://github.com/sindresorhus/type-fest
- Commit: 1b7eed6393d90c7ee010df410dccf2e2ba245427
- License: MIT
- Fixture: `type-fest/object-utilities.ts`
- Source paths:
  - `source/except.d.ts`
  - `source/set-required.d.ts`
  - `source/simplify.d.ts`
  - `source/keys-of-union.d.ts`
  - minimal supporting shapes from `source/internal/index.d.ts`, `source/is-equal.d.ts`, and `source/union-to-intersection.d.ts`
- Curation notes: copied the stricter object utility shapes with compact local support types and an object-model usage file. The fixture exercises key remapping, defaulted options, exact omitted keys, required-key reconstruction, intersection flattening, and key extraction across unions.
