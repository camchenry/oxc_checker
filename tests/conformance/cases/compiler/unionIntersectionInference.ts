// @target: es2022

declare function maybe<T>(value: T | undefined): T;
declare function nullable<T>(value: T | null): T;
declare function falsy<T>(value: T | false): T;
declare function unwrapPromise<T>(value: Promise<T> | T): T;
declare const promiseString: Promise<string>;
declare const intersectionSource: string[] & { extra: number };
declare function extra<T>(value: string[] & T): T;

const maybeValue = maybe("ready");
const nullableValue = nullable("ready");
const falsyValue = falsy("ready");
const promiseValue = unwrapPromise(promiseString);
const directValue = unwrapPromise("ready");
const extraValue = extra(intersectionSource);