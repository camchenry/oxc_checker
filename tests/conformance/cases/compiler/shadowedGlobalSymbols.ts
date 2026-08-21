// @filename: array.ts
export {};
const Array = 1;
const arrayValue = Array;

// @filename: undefined.ts
export {};
const undefined = 1;
const undefinedValue = undefined;

// @filename: parameter.ts
export {};
function shadow(undefined: number) {
  const inside = undefined;
}
const outside = undefined;