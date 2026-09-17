async function useStream<TQueryFnData>(
  streamFn: () => AsyncIterable<TQueryFnData> | Promise<AsyncIterable<TQueryFnData>>,
) {
  const stream = await streamFn();
  for await (const chunk of stream) {
    chunk;
  }
}

async function* asyncGeneratorValues() {
  yield 1;
  yield 2;
}
async function consumeGenerator() {
  for await (const generatedValue of asyncGeneratorValues()) {
    generatedValue;
  }
}

interface TextAsyncIterator {
  next(): Promise<IteratorResult<"chunk", void>>;
}
interface StructuralTextStream {
  [Symbol.asyncIterator](): TextAsyncIterator;
}
declare const structuralStream: StructuralTextStream;
async function consumeStructuralStream() {
  for await (const structuralChunk of structuralStream) {
    structuralChunk;
  }
}

interface InheritedTextStream extends AsyncIterable<"chunk"> {}
declare const inheritedStream: InheritedTextStream;
async function consumeInheritedStream() {
  for await (const inheritedChunk of inheritedStream) {
    inheritedChunk;
  }
}

interface StructuralNumberIterator {
  next(): IteratorResult<1 | 2, void>;
}
interface StructuralNumbers {
  [Symbol.iterator](): StructuralNumberIterator;
}
interface InheritedNumbers extends Iterable<1 | 2> {}
declare const structuralNumbers: StructuralNumbers;
declare const inheritedNumbers: InheritedNumbers;

for (const structuralNumber of structuralNumbers) {
  structuralNumber;
}
for (const inheritedNumber of inheritedNumbers) {
  inheritedNumber;
}

declare const promisedNumbers: Iterable<Promise<1 | 2>>;
for (const promisedNumber of promisedNumbers) {
  promisedNumber;
}
async function consumePromisedNumbers() {
  for await (const awaitedNumber of promisedNumbers) {
    awaitedNumber;
  }
}

interface RecursiveIterableA<T> {
  next(): IteratorResult<T>;
  [Symbol.iterator](): RecursiveIterableA<T>;
}
interface RecursiveIterableB<T> {
  next(): IteratorResult<T>;
  [Symbol.iterator](): RecursiveIterableB<T>;
}
declare const recursiveA: RecursiveIterableA<"recursive">;
declare const recursiveB: RecursiveIterableB<"recursive">;