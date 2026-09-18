// @target: es2022
// @filename: inference.ts
function foo<T>(x: T) {
  return x;
}

const x: string = "hello"
const x1 = foo(x);
const x2 = foo(x1);

function foo2<T, U>(x: T, y: U) {
  return { x, y };
}

const y = foo2("hello", 123);
const y2 = foo2(y.x, y.y);

function foo3<T>(x: T | undefined | null) {
  return x!
}

const f3_1 = foo3("hello");
const f3_2 = foo3(undefined);
const f3_3 = foo3(123 as number);

function defaultOnlyReadU<T = string, U = T>(): U {
  return undefined as any;
}

const defaultOnlyReadUValue = defaultOnlyReadU();

function defaultReadTBeforeU<T = number, U = T>(): [T, U] {
  return undefined as any;
}

const defaultReadTBeforeUValue = defaultReadTBeforeU();

// @filename: contextualSignatures.ts
declare const genericDefaultSource: <T = string, U = T>() => U;
declare const genericObjectTarget: <T, U>(x: T, y: U) => { x: T; y: U };
declare const genericTupleTarget: <T = number, U = T>() => [T, U];
declare const genericIdentitySource: <T>(value: T) => T;
declare const concreteIdentityTarget: (value: string) => string;
declare const widerConstraintSource: <T extends string | number>(value: T) => T;
declare const narrowerConstraintTarget: <T extends string>(value: T) => T;
declare const indexedAccessSource: <T, K extends keyof T>(obj: T, key: K) => T[K];
declare const genericKeyofTarget: <T>(obj: T, key: keyof T) => void;
declare const incompatibleKeyTarget: (text: string, key: boolean) => any;
declare const numberDefaultSource: <T = number>() => T;
declare const stringDefaultTarget: <T = string>() => T;
declare const callableDefaultSource: {
  <T = string, U = T>(): U;
  marker: true;
};
declare const callableObjectTarget: {
  <T, U>(x: T, y: U): { x: T; y: U };
  marker: true;
};
