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

## Redux Toolkit

- Repository: https://github.com/reduxjs/redux-toolkit
- Commit: 7c49510ff5dc6aad7cda24a59ec6c38a1af053be
- License: MIT
- Fixture: `redux-toolkit/create-action.ts`
- Source paths:
  - `packages/toolkit/src/createAction.ts`
  - `packages/toolkit/src/tsHelpers.ts`
  - minimal supporting shape from `packages/toolkit/src/reduxImports.ts`
- Curation notes: copied the action creator and helper type shapes with a compact runtime body and focused usage file. The fixture exercises conditional action creator selection, prepared payload callbacks, inferred meta and error fields, optional and void payloads, type predicate matchers, and matcher-to-action extraction.

## React Hook Form

- Repository: https://github.com/react-hook-form/react-hook-form
- Commit: 1e00a1b18643d6de6cd9a92bcb05b996ac163455
- License: MIT
- Fixture: `react-hook-form/field-path.ts`
- Source paths:
  - `src/types/path/eager.ts`
  - minimal supporting shapes from `src/types/utils.ts`
- Curation notes: adapted the eager field-path utility types into a compact fixture with nested object, tuple, and array usage. The fixture exercises template literal paths, recursive conditional types, tuple key filtering, array path extraction, and path-to-value indexed lookup.

## Remeda

- Repository: https://github.com/remeda/remeda
- Commit: 53d22a60dcd1f854a6d7d7498715ba6f4f56473f
- License: MIT
- Fixture: `remeda/data-first.ts`
- Source paths:
  - `src/map.ts`
  - `src/filter.ts`
  - `src/groupBy.ts`
  - `src/pick.ts`
  - `src/pipe.ts`
  - minimal supporting shapes from `src/internal/types.ts`
- Curation notes: adapted a small data-first collection pipeline with overloads and supporting helper aliases. The fixture exercises type predicate filtering, object and array mapping overloads, partial grouped records, non-empty key lists, object picking, and multi-step pipeline inference.

## Valibot

- Repository: https://github.com/fabian-hiller/valibot
- Commit: c05bf954ada47d5ff953cdfad905cc701b25719c
- License: MIT
- Fixture: `valibot/schema-output.ts`
- Source paths:
  - `library/types.ts`
  - `library/schemas.ts`
- Curation notes: adapted Valibot's schema metadata pattern around `~types` into a small object schema fixture. The fixture exercises string-literal property names, schema input/output extraction, optional defaults, mapped object entries, unioned issue extraction, and value inference through schema builders.

## Zod

- Repository: https://github.com/colinhacks/zod
- Commit: bbc68f990c7e6a5e3f506c56fb04bd0279b9c9b5
- License: MIT
- Fixture: `zod/object-inference.ts`
- Source paths:
  - `src/v3/types.ts`
  - `src/v3/external.ts`
- Curation notes: adapted a compact object schema, optional, array, and pick flow with Zod-style `_input` and `_output` phantom members. The fixture exercises generic class inheritance, output/input helper aliases, builder object inference, optional and array wrappers, object shape mapping, and key-mask based picking.

## Zustand

- Repository: https://github.com/pmndrs/zustand
- Commit: 566b5bf448f4354eb8e35c6243ea3772bdb3be96
- License: MIT
- Fixture: `zustand/store-api.ts`
- Source paths:
  - `src/vanilla.ts`
  - `src/react.ts`
- Curation notes: adapted the vanilla store and bound hook type shapes with a focused counter-store usage. The fixture exercises overloaded call signatures, indexed access on function containers, state creator generics, open mutator interfaces, store-state extraction, callable object intersections, and selector return inference.
