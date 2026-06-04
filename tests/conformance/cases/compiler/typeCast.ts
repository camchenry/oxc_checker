declare const x: any;

type G<T> = T;

const xs = <string>x;
const xu = <unknown>x;
const xn = <number>x;
const xa = <any>x;

const ys = x as string;
const yu = x as unknown;
const yn = x as number;
const ya = x as any;

const gs = x as G<string>;
const gu = x as G<unknown>;
const gn = x as G<number>;
const ga = x as G<any>;

interface i00<T = number> { a: T; }
const i00c00 = (<i00>x)