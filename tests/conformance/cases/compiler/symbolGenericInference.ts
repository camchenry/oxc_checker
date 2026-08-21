type ReturnedQueryFunctionContext<TQueryKey, TPageParam = never> =
  [TPageParam] extends [never]
    ? { queryKey: TQueryKey; pageParam?: unknown }
    : { queryKey: TQueryKey; pageParam: TPageParam };
type ReturnedQueryFunction<T, TQueryKey, TPageParam = never> =
  (queryContext: ReturnedQueryFunctionContext<TQueryKey, TPageParam>) => T | Promise<T>;

function makeReturnedQuery<TData, TQueryKey>(): ReturnedQueryFunction<TData, TQueryKey> {
  return async (context) => undefined as TData;
}

declare function acceptEvent<T extends { kind: "event"; value: string }>(value: T): T;
const contextualObjectResult = acceptEvent({ kind: "event", value: "payload" });

declare function firstElement<T>(values: T[]): T;
declare function inferPair<T, U>(value: [T, U]): [T, U];
declare function inferTail<T extends unknown[]>(value: [string, ...T]): T;
const firstValue = firstElement([1, 2]);
const pairValue = inferPair([1, "ready"] as [number, string]);
const tailValue = inferTail(["start", 1, true] as [string, number, boolean]);

declare function maybe<T>(value: T | undefined): T;
declare function nullable<T>(value: T | null): T;
declare function falsy<T>(value: T | false): T;
declare function unwrapPromise<T>(value: Promise<T> | T): T;
declare const promiseString: Promise<string>;
const maybeValue = maybe("ready");
const nullableValue = nullable("ready");
const falsyValue = falsy("ready");
const promiseValue = unwrapPromise(promiseString);
const directValue = unwrapPromise("ready");

declare const intersectionSource: string[] & { extra: number };
declare function inferExtra<T>(value: string[] & T): T;
const extraValue = inferExtra(intersectionSource);

function selectOverload(x: string): string;
function selectOverload(x: number): number;
function selectOverload(x: string | number): string | number { return x; }
const selectedString = selectOverload("ready");
const selectedNumber = selectOverload(123);

function explicitOverload<T>(x: T): T;
function explicitOverload<T, U>(x: T): U;
function explicitOverload(x: unknown): unknown { return x; }
const explicitOverloadValue = explicitOverload<number, string>(123);

interface Picker {
  pick(x: string): string;
  pick(x: number): number;
}
declare const picker: Picker;
const pickedString = picker.pick("ready");
const pickedNumber = picker.pick(123);