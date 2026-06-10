// @filename: a.ts
type T1 = 'A' | 'A';

type T2 = string | string | number;

type T3 = { a: string } & { a: string };

type T4 = [1, 2, 3] | [1, 2, 3];

type StringA = string;
type StringB = string;
type T5 = StringA | StringB;

const fn = (a?: string | undefined) => {};

// @filename: b.ts
type T1 = 'A' | 'B';

type T2 = string | number | boolean;

type T3 = { a: string } & { b: string };

type T4 = [1, 2, 3] | [1, 2, 3, 4];

type StringA = string;
type NumberB = number;
type T5 = StringA | NumberB;

const fn = (a?: string) => {};