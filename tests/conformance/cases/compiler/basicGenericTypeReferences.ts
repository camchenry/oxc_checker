// @target: es2022
type Box<T> = { value: T };
type DefaultBox<T = number> = { value: T };
type SelfDefault<T = T> = { value: T };
type ForwardDefault<T = U, U = string> = { t: T; u: U };
type DependentDefault<T = string, U = T> = { t: T; u: U };

function box<T>(x: T): Box<T> {
  return { value: x };
}

const explicit: Box<string> = { value: "test" };
const inferred = box(123);
const fromExplicitCall = box<string>("test");
declare const defaultBox: DefaultBox;
declare const selfDefault: SelfDefault;
declare const forwardDefault: ForwardDefault;
declare const dependentDefault: DependentDefault;