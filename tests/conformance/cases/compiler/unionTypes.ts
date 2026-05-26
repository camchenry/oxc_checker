// @target: es2022

function unionized(x: string | number | boolean) {
  return x
}

const unionReturn = unionized("hello");

function padLeft(value: string, padding: string | number) {
  return value
}

let indentedString = padLeft("Hello world", true);

export type Expression = BooleanLogicExpression | 'true' | 'false';
export type BooleanLogicExpression = ['and', ...Expression[]] | ['not', Expression]; 

type AllLiterals = 'string' | false | 123 | 123n | `test` | `test${string}`