// @target: es2022
function foo<T>(x: T) {
  return x;
}

const x: string = "hello"
const x1 = foo(x);
const x2 = foo(x1);

function foo2<T, U>(x: T, y: U) {
  return { x, y };
}

const y = foo2("hello", 123);
const y2 = foo2(y.x, y.y);

function foo3<T>(x: T | undefined | null) {
  return x!
}

const f3_1 = foo3("hello");
const f3_2 = foo3(undefined);
const f3_3 = foo3(123 as number);