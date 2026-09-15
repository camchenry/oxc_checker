// @strict: true

// @filename: combinedParameters.ts
const stringOrNumberCallback:
    ((value: string) => { stringResult: true }) &
    ((value: number) => { numberResult: true }) = value => ({
    stringResult: typeof value === "string",
    numberResult: typeof value === "number",
});

// @filename: arityFiltering.ts
const oneParameterCallback:
    ((value: string) => void) &
    ((value: number, extra: boolean) => void) = value => {};

// @filename: incompatibleTypeParameters.ts
const incompatibleTypeParameters:
    (<T>(value: T) => T) &
    ((value: string) => string) = value => value;