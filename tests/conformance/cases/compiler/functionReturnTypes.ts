// @target: es2022

function empty() {

}

function emptyVoid(): void {
  
}

class EmptyGetter {
  public get x() {

  }
}

function returnsBig() {
  return 1n
}

function returnsBig2() {
  if (1 + 1 === 4) {
    return 0n;
  }
  return 1n
}

function assertsIsString(x: unknown): asserts x is string {
  if (typeof x !== "string") {
    throw new Error("Not a string");
  }
}

function isString(x: unknown): x is string {
  return typeof x === "string";
}

function genericIsString<T>(x: T): x is T {
  return typeof x === "string";
}

function assertsGenericIsString<T>(x: T): asserts x is T {
  if (typeof x !== "string") {
    throw new Error("Not a string");
  }
}