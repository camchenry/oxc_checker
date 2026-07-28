// @target: es2022

const numberResult = (0, 42);
const stringResult = (0, "result");
const booleanResult = (false, true);
const referenceResult = (numberResult, stringResult);
const nestedResult = (0, (1, "nested"));
