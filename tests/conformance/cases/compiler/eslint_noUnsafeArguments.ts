// @filename: a.ts
declare function foo(arg1: string, arg2: number, arg3: string): void;

const anyTyped = 1 as any;

foo(...anyTyped);
foo(anyTyped, 1, 'a');

const anyArray: any[] = [];
foo(...anyArray);

const tuple1 = ['a', anyTyped, 'b'] as const;
foo(...tuple1);

const tuple2 = [1] as const;
foo('a', ...tuple2, anyTyped);

declare function bar(arg1: string, arg2: number, ...rest: string[]): void;
const x = [1, 2] as [number, ...number[]];
bar('a', ...x, anyTyped);

declare function baz(arg1: Set<string>, arg2: Map<string, string>): void;
baz(new Set<any>(), new Map<any, string>());

// @filename: b.ts
declare function foo(arg1: string, arg2: number, arg3: string): void;

foo('a', 1, 'b');

const tuple1 = ['a', 1, 'b'] as const;
foo(...tuple1);

declare function bar(arg1: string, arg2: number, ...rest: string[]): void;
const array: string[] = ['a'];
bar('a', 1, ...array);

declare function baz(arg1: Set<string>, arg2: Map<string, string>): void;
baz(new Set<string>(), new Map<string, string>());

// @filename: c.ts
declare function foo(arg1: unknown, arg2: Set<unknown>, arg3: unknown[]): void;
foo(1 as any, new Set<any>(), [] as any[]);