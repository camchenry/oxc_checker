// @target: es2022

declare function mixedIndexedAccess<T>(): readonly [T['single'], T["double"]];

declare function singleTuple(): readonly ['entry'];
declare function doubleTuple(): readonly ["entry"];
declare function mixedTuple(): readonly ['same', "same"];

declare function singleObject(): { kind: 'single' };
declare function doubleObject(): { kind: "double" };
declare function mixedObject(): { single: 'same'; double: "same" };

declare function singleProperty(): { 'not-name': string };
declare function doubleProperty(): { "not-name": string };
declare function mixedProperty(): { 'same-name': string; "same-name"?: string };

declare function quotationEdges(): readonly ['say "hello"', "it's", 'both \'"', 'C:\\temp'];

const synthesizedLiteral = 'synthesized' as const;