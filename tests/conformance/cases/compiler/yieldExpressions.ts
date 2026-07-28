// @target: es2022

function* _innerGenerator(): Generator<number, "inner", boolean> {
  const _input = yield 0;
  return "inner";
}

function* _typedGenerator(): Generator<number, string, boolean> {
  const _input = yield 1;
  const _bareInput = yield;
  const _delegatedReturn = yield* _innerGenerator();
  const _arrayReturn = yield* [1, 2];
  return "done";
}

async function* _asyncGenerator(): AsyncGenerator<string, void, Date> {
  const _input = yield "value";
  return;
}

function* _untypedGenerator() {
  const _input = yield 1;
}