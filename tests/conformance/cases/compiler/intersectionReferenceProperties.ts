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