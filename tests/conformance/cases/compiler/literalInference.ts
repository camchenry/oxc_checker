// @target: es2022

function identity<T>(value: T): T {
  return value;
}

function box<T>(value: T): { value: T } {
  return { value };
}

const preservedLiteral = identity("ready");
const widenedLiteral = box("ready");
