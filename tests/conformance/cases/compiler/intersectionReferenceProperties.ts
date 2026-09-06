interface A {
    a: string;
}

interface Left {
    kind: "left";
}

interface Right {
    kind: "right";
}

declare const value: A & { b: number };
declare const impossible: Left & Right;
export const target: { a: string; b: number } = value;
export const numeric: number = impossible;

declare const wideThenNarrow: { value: string } & { value: "x" };
declare const narrowThenWide: { value: "x" } & { value: string };
export const narrowFromWideThenNarrow: { value: "x" } = wideThenNarrow;
export const narrowFromNarrowThenWide: { value: "x" } = narrowThenWide;

declare const optionalThenRequired: { value?: "x" } & { value: string };
declare const requiredThenOptional: { value: string } & { value?: "x" };
export const requiredFromOptionalThenRequired: { value: string } = optionalThenRequired;
export const requiredFromRequiredThenOptional: { value: string } = requiredThenOptional;