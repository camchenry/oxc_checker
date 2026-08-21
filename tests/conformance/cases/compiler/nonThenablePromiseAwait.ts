export {};

interface Promise<T> {
  value: T;
}

declare const promise: Promise<number>;
const value = await promise;