// @target: es2022

declare function literalOverload(x: string): "wide";
declare function literalOverload(x: "ready"): "literal";

declare function genericOverload<T>(x: T): T[];
declare function genericOverload(x: string): string;

declare function tiedOverload(x: string, y?: number): "first";
declare function tiedOverload(x: string): "second";

declare function tupleRestOverload(...args: [string]): "one";
declare function tupleRestOverload(...args: [string, number]): "two";

declare function optionalTupleRestOverload(...args: [string, number?]): "optional";
declare function optionalTupleRestOverload(...args: [string, number, boolean]): "three";

const literalResult = literalOverload("ready");
const genericResult = genericOverload("ready");
const tiedResult = tiedOverload("ready");
const tupleRestOne = tupleRestOverload("ready");
const tupleRestTwo = tupleRestOverload("ready", 1);
const optionalTupleRestOne = optionalTupleRestOverload("ready");
const optionalTupleRestTwo = optionalTupleRestOverload("ready", 1);
const optionalTupleRestThree = optionalTupleRestOverload("ready", 1, true);