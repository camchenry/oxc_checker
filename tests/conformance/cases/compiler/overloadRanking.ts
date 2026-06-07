// @target: es2022

declare function literalOverload(x: string): "wide";
declare function literalOverload(x: "ready"): "literal";

declare function genericOverload<T>(x: T): T[];
declare function genericOverload(x: string): string;

declare function tiedOverload(x: string, y?: number): "first";
declare function tiedOverload(x: string): "second";

const literalResult = literalOverload("ready");
const genericResult = genericOverload("ready");
const tiedResult = tiedOverload("ready");