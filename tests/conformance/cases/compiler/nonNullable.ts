type T0 = string | null | undefined;
type T1 = NonNullable<T0>;
type T2 = NonNullable<T0 | number | boolean | {}>;
type T3 = NonNullable<any>;
type T4 = NonNullable<unknown>;
type T5 = NonNullable<never>;
type T6 = NonNullable<Array<number>>;
type T7 = NonNullable<NonNullable<NonNullable<T0>>>;
type T8 = "literal" | 1 | true;
type T9 = bigint | symbol;
type T10 = null | undefined;
type T11 = void;
type T12<T> = T;
type T13<T extends {}> = T;

const inferredEmpty = {};
({}, {});