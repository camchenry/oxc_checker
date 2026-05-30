const promise = new Promise((resolve, reject) => resolve('value'));
promise;

async function returnsPromise() {
  return 'value';
}
returnsPromise().then(() => {});

Promise.reject('value').catch();

Promise.reject('value').finally();

[1, 2, 3].map(async x => x + 1);

const promise = new Promise((resolve, reject) => resolve('value'));
await promise;

async function returnsPromise() {
  return 'value';
}

void returnsPromise();

returnsPromise().then(
  () => {},
  () => {},
);

Promise.reject('value').catch(() => {});

await Promise.reject('value').finally(() => {});

await Promise.all([1, 2, 3].map(async x => x + 1));

// checkThenables

declare function createPromiseLike(): PromiseLike<string>;

createPromiseLike();
await createPromiseLike();

interface MyThenable {
  then(onFulfilled: () => void, onRejected: () => void): MyThenable;
}

declare function createMyThenable(): MyThenable;

await createMyThenable();

// ignoreVoid

async function returnsPromise() {
  return 'value';
}
void returnsPromise();

void Promise.reject('value');

// ignoreIIFE

await (async function () {
  await res(1);
})();

(async function () {
  await res(1);
})();