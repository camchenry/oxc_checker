// @filename: a.ts
declare const arr: number[];

delete arr[0];

// @filename: b.ts
declare const arr: number[];

arr.splice(0, 1);