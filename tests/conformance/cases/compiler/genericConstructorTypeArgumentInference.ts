// @filename: box.ts
export class Box<T> {
    constructor(readonly value: T) {}
}

export class DefaultBox<T = string> {
    constructor(readonly value?: T) {}
}

export class UnknownBox<T> {
    value!: T;
}

// @filename: inference.ts
import { Box, DefaultBox, UnknownBox } from "./box";

const concrete = new Box({ count: 1 });
const concreteValue = concrete.value;

function preserve<T>(value: T) {
    let inferred = new Box(value);
    const forward: Box<T> = inferred;
    inferred = forward;
    return inferred;
}

const preserved = preserve({ label: "value" });
const explicit = new Box<string>("value");
const defaulted = new DefaultBox();
const unresolved = new UnknownBox();

// @filename: hierarchy.ts
export class Base<T> {
    value!: T;
    self(): this {
        return this;
    }
}

export class Derived extends Base<string> {}
export class Middle<T> extends Base<T[]> {}
export class Leaf extends Middle<number> {}

const inheritedValue = new Derived().value;
const inheritedThis = new Derived().self();
const nestedInheritedValue = new Leaf().value;

// @filename: indexed.ts
import { Box } from "./box";
import { Base, Derived, Leaf } from "./hierarchy";

type OwnIndexed = Box<{ count: number }>["value"];
type InheritedIndexed = Derived["value"];
type InheritedThisIndexed = Derived["self"];
type NestedInheritedIndexed = Leaf["value"];

type ValueOf<T extends Base<unknown>> = T["value"];
type ValuesOf<T extends Base<unknown>> = ValueOf<T>[];
type ExpandedArrayAlias = ValuesOf<Derived>;