// @target: es2022
// @module: esnext
// @allowImportingTsExtensions: true

// @filename: module.ts
export type Value = { value: string };
export type Box<T> = { value: T };

export namespace Nested {
  export let runtime = 0;
  export type Value = 42;
}

// @filename: main.ts
type ImportedValue = import("./module.ts").Value;
type ImportedBox = import("./module.ts").Box<number>;
type ImportedNestedValue = import("./module.ts").Nested.Value;