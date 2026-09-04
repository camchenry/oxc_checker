// @filename: iterator.ts
interface Iterator<T> {
  value: T;
}

interface Map<K, V> {
  [Symbol.iterator](): Iterator<readonly [K, V]>;
}

declare const map: Map<string, number>;
// @ts-expect-error Local Iterator is not the global iterator protocol.
export const mapObject = Object.fromEntries(map);

// @filename: iterable.ts
interface Iterable<T> {
  local: T;
}

declare function unwrap<T>(value: Iterable<T>): T;
declare const iterable: Iterable<"iterable">;
export const unwrapped = unwrap(iterable);

// @filename: promise.ts
interface Promise<T> {
  value: T;
}

declare const promise: Promise<number>;
export const awaited = await promise;

// @filename: record.ts
type Record<K, V> = {
  key: K;
  value: V;
};

declare const record: Record<"key", 42>;
export const recordKey = record.key;
export const recordValue = record.value;

// @filename: object.ts
interface Object {
  local: "object";
}

declare const object: Object;
export const objectProperty = object.local;

// @filename: array.ts
interface Array<T> {
  local: T;
}

declare const array: Array<"array">;
export const arrayProperty = array.local;
