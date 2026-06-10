// @filename: a.ts
declare const promise: Promise<number>;
const spreadPromise = { ...promise };

declare function getObject(): Record<string, string>;
const getObjectSpread = { ...getObject };

declare const map: Map<string, number>;
const mapSpread = { ...map };

declare const userName: string;
const characters = [...userName];

// @filename: b.ts
declare class Box {
  value: number;
}
const boxSpread = { ...Box };

declare const instance: Box;
const instanceSpread = { ...instance };

// @filename: c.ts
declare const promise: Promise<number>;
const spreadPromise = { ...(await promise) };

declare function getObject(): Record<string, string>;
const getObjectSpread = { ...getObject() };

declare const map: Map<string, number>;
const mapObject = Object.fromEntries(map);

declare const userName: string;
const characters = userName.split('');