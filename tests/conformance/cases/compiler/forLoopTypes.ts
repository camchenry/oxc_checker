// @filename: classic.ts
for (let index = 0; index < 2; index++) {
  index;
}

// @filename: forIn.ts
const record = { first: 1, second: 2 };
for (const key in record) {
  key;
}

// @filename: forOf.ts
const tuple = ["text", 42] as const;
for (const value of tuple) {
  value;
}

// @filename: forAwaitOfSync.ts
async function consumeSyncPromises() {
  const promises = [Promise.resolve(1), Promise.resolve(2)];
  for await (const awaitedValue of promises) {
    awaitedValue;
  }
}

// @filename: forAwaitOfAsync.ts
declare const asyncValues: AsyncIterable<string>;
async function consumeAsyncIterable() {
  for await (const asyncValue of asyncValues) {
    asyncValue;
  }
}