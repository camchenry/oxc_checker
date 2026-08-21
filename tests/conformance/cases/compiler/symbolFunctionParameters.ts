// @filename: declared.ts
export {};
function declaredParameters(a: number, b: string, c: boolean) {}

// @filename: optional.ts
export {};
declare function optionalParameter(value?: number): number;

// @filename: annotation.ts
export {};
declare function pipe<A extends any[], B>(callback: (...args: A) => B): B;

// @filename: predicates.ts
export {};
declare function acceptsPredicate<T, S extends T>(
  predicate: (value: T) => value is S,
  assertion: (value: unknown) => asserts value is string,
  thisPredicate: (this: unknown) => this is { ready: true },
  thisAssertion: (this: unknown) => asserts this is { ready: true },
  bareAssertion: (value: unknown) => asserts value,
  bareThisAssertion: (this: unknown) => asserts this,
): void;

// @filename: callbackReturn.ts
export {};
declare function useCallback<T>(callback: () => T): T;
declare function configureReturn<T>(options: { create: () => T }): T;
const callbackValue = useCallback(() => 1);
const objectCallbackValue = configureReturn({ create: () => ({ value: 1 }) });

// @filename: objectCallbacks.ts
export {};
declare function configureObject<T>(options: {
  create: () => T;
  consume: (value: T) => void;
}): T;
const objectResult = configureObject({
  create: () => ({ value: 1 }),
  consume: item => {
    const objectDerivedValue = item.value;
  },
});

// @filename: tupleCallbacks.ts
export {};
declare function configureTuple<T>(callbacks: [() => T, (value: T) => void]): T;
const tupleResult = configureTuple([
  () => ({ value: 1 }),
  item => {
    const tupleDerivedValue = item.value;
  },
]);