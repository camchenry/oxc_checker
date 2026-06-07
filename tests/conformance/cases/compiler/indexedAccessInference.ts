// @target: es2022

declare function get<T, K extends keyof T>(obj: T, key: K): T[K];

const value = get({ value: 1, name: "ready" }, "value");
const name = get({ value: 1, name: "ready" }, "name");