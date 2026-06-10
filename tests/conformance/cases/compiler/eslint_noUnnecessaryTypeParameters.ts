// @filename: a.ts
function second<A, B>(a: A, b: B): B {
  return b;
}

function parseJSON<T>(input: string): T {
  return JSON.parse(input);
}

function printProperty<T, K extends keyof T>(obj: T, key: K) {
  console.log(obj[key]);
}

// @filename: b.ts
function second<B>(a: unknown, b: B): B {
  return b;
}

function parseJSON(input: string): unknown {
  return JSON.parse(input);
}

function printProperty<T>(obj: T, key: keyof T) {
  console.log(obj[key]);
}

// T appears twice: in the type of arg and as the return type
function identity<T>(arg: T): T {
  return arg;
}

// T appears twice: "keyof T" and in the inferred return type (T[K]).
// K appears twice: "key: K" and in the inferred return type (T[K]).
function getProperty<T, K extends keyof T>(obj: T, key: K) {
  return obj[key];
}

// @filename: c.ts
declare function length<T>(array: ReadonlyArray<T>): number;

declare function length2(array: ReadonlyArray<unknown>): number;