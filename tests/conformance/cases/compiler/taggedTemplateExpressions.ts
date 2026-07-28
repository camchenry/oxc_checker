// @target: es2022

declare function stringTag(template: any, ...values: any[]): string;
declare function literalTag(template: any, ...values: any[]): "literal";
declare function genericTag<T>(template: any, value: T): T;
declare function curriedTag(template: any): (value: string) => number;

const stringResult = stringTag`hello`;
const literalResult = literalTag`literal`;
const genericResult = genericTag`value: ${42}`;
const curriedResult = curriedTag`value`("input");
