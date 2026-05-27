declare const x: any;

const xs = <string>x;
const xu = <unknown>x;
const xn = <number>x;
const xa = <any>x;``

interface i00<T = number> { a: T; }
const i00c00 = (<i00>x)