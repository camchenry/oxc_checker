// @filename: arrow.ts
export {};
const predicate = () => false;

// @filename: async.ts
export {};
async function returnsString() { return "value"; }
async function empty() {}
async function unwrapPromise(value: Promise<number>) { return value; }
async function preserveGeneric<T>(value: T) { return value; }
const returnsNumber = async () => 1;
const stringResult = returnsString();
const emptyResult = empty();
const unwrappedResult = unwrapPromise(Promise.resolve(1));
const genericResult = preserveGeneric("value");
const numberResult = returnsNumber();