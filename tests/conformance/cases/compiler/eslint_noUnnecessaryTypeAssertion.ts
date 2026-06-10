// @filename: a.ts
const foo1 = 3;
const bar = foo!;

const foo1_1 = <number>3;

const foo2 = <number>(3 + 5);
const foo2_1 = 3 as number;

type Foo = number;
const foo3 = <Foo>(3 + 5);

function foo4(x: number): number {
  return x!; // unnecessary non-null
}

let foo5 = 'foo' as const;

function foo6(x: number | undefined): number {
  return x!;
}