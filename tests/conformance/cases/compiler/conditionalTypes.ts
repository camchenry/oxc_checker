type ConcreteTrue = number extends number ? boolean : string;
type ConcreteFalse = number extends string ? boolean : string;

declare const concreteTrue: number extends number ? boolean : string;
declare const concreteFalse: number extends string ? boolean : string;

declare function choose<T>(): T extends string ? boolean : number;
const distributed = choose<string | number>();

declare function unresolvedConditional<T>(): T extends string ? number : boolean;
