// @filename: explicit.ts
export {};
function explicitIdentity<T>(value: T) { return value; }
const explicitResult = explicitIdentity<string>("test");

// @filename: object.ts
export {};
function objectBox<T>(value: T) { return { value }; }
const objectResult = objectBox(123);

// @filename: references.ts
export {};
type ResultBox<T> = { value: T };
function referenceBox<T>(value: T): ResultBox<T> { return { value }; }
const explicitBox: ResultBox<string> = { value: "test" };
const inferredBox = referenceBox(123);
const calledBox = referenceBox<string>("test");

// @filename: constraints.ts
export {};
interface ConstraintA { a: number }
declare const constraintA: ConstraintA;
declare const constrainedFunctionValue: <T extends ConstraintA>(value: T) => T;
declare function constrainedFunction<T extends ConstraintA, U extends T = T>(value?: T, other?: U): [T, U];
declare function fallbackToConstraint<T extends string>(): T;
const fromConstraint = constrainedFunction();
const fromConstraintInference = constrainedFunction(constraintA);
const stringConstraint = fallbackToConstraint();

// @filename: class.ts
export {};
class GenericCallFoo {
  doThing(value: { a: number }) { return { b: value.a }; }
}
const classInstance = new GenericCallFoo();
const classMethodResult = classInstance.doThing({ a: 12 });

// @filename: inference.ts
export {};
function inferredIdentity<T>(value: T) { return value; }
const inferredNumber = inferredIdentity(123);
const inferredString = inferredIdentity("test");
const inferredBoolean = inferredIdentity(true);

// @filename: nonNull.ts
export {};
function nonNull<T>(value: T | undefined | null) { return value!; }
const nonNullString = nonNull("hello");
const nonNullUndefined = nonNull(undefined);
const nonNullNumber = nonNull(123 as number);

// @filename: genericOverload.ts
export {};
declare function genericPick<T>(value: T[]): T;
declare function genericPick<T>(value: T): T;
const genericOverloadResult = genericPick("ready");
