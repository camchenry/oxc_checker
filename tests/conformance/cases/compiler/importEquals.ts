// @target: es2022
// @module: commonjs
// @allowImportingTsExtensions: true

// @filename: named.ts
export const answer: 42 = 42;

// @filename: assigned.ts
const assigned: { value: "assigned" } = { value: "assigned" };
export = assigned;

// @filename: main.ts
namespace Local {
  export const value: "local" = "local";
}

import LocalAlias = Local;
import ValueAlias = Local.value;
import named = require("./named.ts");
import assigned = require("./assigned.ts");

const local = LocalAlias.value;
const value = ValueAlias;
const answer = named.answer;
const assignedValue = assigned.value;