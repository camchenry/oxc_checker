type DirectInfer = string extends infer U ? U : never;
type PropertyInfer = { value: number } extends { value: infer U } ? U : never;
type MissingProperty = { other: string } extends { value: infer U } ? U : never;
type ConstrainedInferTrue = "ready" extends infer U extends string ? U : never;
type ConstrainedInferFalse = number extends infer U extends string ? U : never;
type RepeatedInfer = { a: string; b: number } extends { a: infer U; b: infer U } ? U : never;
type TupleRestInfer = [string, number, boolean] extends [infer Head, ...infer Rest] ? Rest : never;
type ArrayElementInfer = string[] extends (infer T)[] ? T : never;
type UnionInfer = { value: string } | { value: number } extends { value: infer U } ? U : never;

declare const directInfer: string extends infer U ? U : never;
declare const propertyInfer: { value: number } extends { value: infer U } ? U : never;
declare const missingProperty: { other: string } extends { value: infer U } ? U : never;
declare const constrainedInferTrue: "ready" extends infer U extends string ? U : never;
declare const constrainedInferFalse: number extends infer U extends string ? U : never;
declare const repeatedInfer: { a: string; b: number } extends { a: infer U; b: infer U } ? U : never;
declare const tupleRestInfer: [string, number, boolean] extends [infer Head, ...infer Rest] ? Rest : never;
declare const arrayElementInfer: string[] extends (infer T)[] ? T : never;
declare const unionInfer: { value: string } | { value: number } extends { value: infer U } ? U : never;