namespace Values {
  export const literal: "value" = "value";
  const hidden = 1;
  export type TypeOnly = string;

  export function make(): number {
    return hidden;
  }

  export namespace Nested {
    export const flag: true = true;

    export namespace Deep {
      export const count: 2 = 2;
    }
  }
}

namespace Values {
  export const merged: 42 = 42;
}

const literal = Values.literal;
const made = Values.make();
const flag = Values.Nested.flag;
const count = Values.Nested.Deep.count;
const merged = Values.merged;