// @filename: a.ts
await 'value';

const createValue = () => 'value';
await createValue();

// @filename: b.ts
await Promise.resolve('value');

const createValue = async () => 'value';
await createValue();

// @filename: c.ts
async function syncIterable() {
  const arrayOfValues = [1, 2, 3];
  for await (const value of arrayOfValues) {
    console.log(value);
  }
}

async function syncIterableOfPromises() {
  const arrayOfPromises = [
    Promise.resolve(1),
    Promise.resolve(2),
    Promise.resolve(3),
  ];
  for await (const promisedValue of arrayOfPromises) {
    console.log(promisedValue);
  }
}

// @filename: d.ts
async function syncIterable() {
  const arrayOfValues = [1, 2, 3];
  for (const value of arrayOfValues) {
    console.log(value);
  }
}

async function syncIterableOfPromises() {
  const arrayOfPromises = [
    Promise.resolve(1),
    Promise.resolve(2),
    Promise.resolve(3),
  ];
  for (const promisedValue of await Promise.all(arrayOfPromises)) {
    console.log(promisedValue);
  }
}

async function validUseOfForAwaitOnAsyncIterable() {
  async function* yieldThingsAsynchronously() {
    yield 1;
    await new Promise(resolve => setTimeout(resolve, 1000));
    yield 2;
  }

  for await (const promisedValue of yieldThingsAsynchronously()) {
    console.log(promisedValue);
  }
}

// @filename: e.ts
function makeSyncDisposable(): Disposable {
  return {
    [Symbol.dispose](): void {
      // Dispose of the resource
    },
  };
}

async function shouldNotAwait() {
  await using resource = makeSyncDisposable();
}

// @filename: f.ts
function makeSyncDisposable(): Disposable {
  return {
    [Symbol.dispose](): void {
      // Dispose of the resource
    },
  };
}

async function shouldNotAwait() {
  using resource = makeSyncDisposable();
}

function makeAsyncDisposable(): AsyncDisposable {
  return {
    async [Symbol.asyncDispose](): Promise<void> {
      // Dispose of the resource asynchronously
    },
  };
}

async function shouldAwait() {
  await using resource = makeAsyncDisposable();
}