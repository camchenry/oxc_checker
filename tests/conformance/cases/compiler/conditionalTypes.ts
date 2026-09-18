type ConcreteTrue = number extends number ? boolean : string;
type ConcreteFalse = number extends string ? boolean : string;

declare const concreteTrue: number extends number ? boolean : string;
declare const concreteFalse: number extends string ? boolean : string;

declare function choose<T>(): T extends string ? boolean : number;
const distributed = choose<string | number>();

declare function unresolvedConditional<T>(): T extends string ? number : boolean;

type Primitive = null | undefined | string | number | boolean | symbol | bigint;
type IsTuple<T extends ReadonlyArray<any>> = number extends T["length"] ? false : true;
type DistributiveBoolean<T> = T extends string ? false : true;
type OneAnyBranch<T> = T extends string ? any : number;
type BooleanTarget = boolean;
type TrueTarget = true;
type ObjectTarget = object;
type EmptyObjectTarget = {};
