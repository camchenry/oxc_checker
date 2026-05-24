// @target: es2022
function foo<T>(x: T) {
  return x;
}

const x: string = "hello"
const x1 = foo(x);
const x2 = foo(x1);