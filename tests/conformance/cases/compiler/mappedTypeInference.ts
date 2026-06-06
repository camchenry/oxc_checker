// @target: es2022

declare function unwrap<T>(value: { [P in keyof T]: T[P] }): T;
declare function unwrapReadonly<T>(value: { readonly [P in keyof T]: T[P] }): T;
declare function pickish<T, K extends keyof T>(value: { [P in K]: T[P] }): T;

const objectValue = unwrap({ value: 1, name: "ready" });
const arrayValue = unwrap([1, 2] as number[]);
const tupleValue = unwrap([1, "ready"] as [number, string]);
const readonlyTupleValue = unwrapReadonly([1, "ready"] as readonly [number, string]);
const pickValue = pickish({ value: 1 });