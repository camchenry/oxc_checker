// @target: es2022

let numberValue = 1;
let bigintValue: bigint = 1n;
let anyValue: any = 1;
const numberObject = { value: 1 };

const _prefixIncrement = ++numberValue;
const _postfixIncrement = numberValue++;
const _prefixDecrement = --numberValue;
const _postfixDecrement = numberValue--;
const _prefixBigInt = ++bigintValue;
const _postfixBigInt = bigintValue--;
const _prefixAny = ++anyValue;
const _memberIncrement = ++numberObject.value;
const _computedMemberDecrement = numberObject["value"]--;