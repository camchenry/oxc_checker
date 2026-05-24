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