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