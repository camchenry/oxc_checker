// @target: es2022
type Box<T> = { value: T };

function box<T>(x: T): Box<T> {
  return { value: x };
}

const explicit: Box<string> = { value: "test" };
const inferred = box(123);
const fromExplicitCall = box<string>("test");