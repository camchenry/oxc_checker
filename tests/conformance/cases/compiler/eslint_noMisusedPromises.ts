// @filename: a.ts
const promise = Promise.resolve('value');

if (promise) {
  // Do something
}

const val = promise ? 123 : 456;

[1, 2, 3].filter(() => promise);

while (promise) {
  // Do something
}

// @filename: b.ts
const promise = Promise.resolve('value');

// Always `await` the Promise in a conditional
if (await promise) {
  // Do something
}

const val = (await promise) ? 123 : 456;

const returnVal = await promise;
[1, 2, 3].filter(() => returnVal);

while (await promise) {
  // Do something
}

// @filename: c.ts
[1, 2, 3].forEach(async value => {
  await fetch(`/${value}`);
});

new Promise<void>(async (resolve, reject) => {
  await fetch('/');
  resolve();
});

document.addEventListener('click', async () => {
  console.log('synchronous call');
  await fetch('/');
  console.log('synchronous call');
});

interface MySyncInterface {
  setThing(): void;
}
class MyClass implements MySyncInterface {
  async setThing(): Promise<void> {
    this.thing = await fetchThing();
  }
}

// @filename: d.ts
// for-of puts `await` in outer context
for (const value of [1, 2, 3]) {
  await doSomething(value);
}

// If outer context is not `async`, handle error explicitly
Promise.all(
  [1, 2, 3].map(async value => {
    await doSomething(value);
  }),
).catch(handleError);

// Use an async IIFE wrapper
new Promise((resolve, reject) => {
  // combine with `void` keyword to tell `no-floating-promises` rule to ignore unhandled rejection
  void (async () => {
    await doSomething();
    resolve();
  })();
});

// Name the async wrapper to call it later
document.addEventListener('click', () => {
  const handler = async () => {
    await doSomething();
    otherSynchronousCall();
  };

  try {
    synchronousCall();
  } catch (err) {
    handleSpecificError(err);
  }

  handler().catch(handleError);
});

interface MyAsyncInterface {
  setThing(): Promise<void>;
}
class MyClass implements MyAsyncInterface {
  async setThing(): Promise<void> {
    this.thing = await fetchThing();
  }
}

// @filename: e.ts
const getData = () => fetch('/');

console.log({ foo: 42, ...getData() });

const awaitData = async () => {
  await fetch('/');
};

console.log({ foo: 42, ...awaitData() });

// @filename: f.ts
const getData = () => fetch('/');

console.log({ foo: 42, ...(await getData()) });

const awaitData = async () => {
  await fetch('/');
};

console.log({ foo: 42, ...(await awaitData()) });