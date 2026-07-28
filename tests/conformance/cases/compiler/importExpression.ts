// @target: es2022
// @module: esnext
// @allowImportingTsExtensions: true

// @filename: module.ts
export const answer: 42 = 42;
export default "default";

// @filename: main.ts
const modulePromise = import("./module.ts");
const moduleNamespace = await modulePromise;
const importedAnswer = moduleNamespace.answer;
const importedDefault = moduleNamespace.default;