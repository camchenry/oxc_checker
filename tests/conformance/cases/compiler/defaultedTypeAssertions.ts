declare const assertionSource: any;
interface AssertionBox<T = number> { value: T }
interface SelfDefault<T = T> { value: T }
interface ForwardDefault<T = U, U = string> { t: T; u: U }
type Identity<T> = T;
type DefaultIdentity<T = string> = T;
type AliasBox<T> = { value: T };

const assertedString = <string>assertionSource;
const assertedUnknown = <unknown>assertionSource;
const assertedNumber = <number>assertionSource;
const assertedAny = <any>assertionSource;
const identityString = assertionSource as Identity<string>;
const identityAny = <Identity<any>>assertionSource;
const defaultIdentity = assertionSource as DefaultIdentity;
const aliasBox = assertionSource as AliasBox<string>;
const boxed = (<AssertionBox>assertionSource);
const explicitDefaultBox = (<AssertionBox<number>>assertionSource);
const boxedValue = (<AssertionBox>assertionSource).value;
const explicitBoxedValue = (<AssertionBox<string>>assertionSource).value;
const selfDefaultValue = (<SelfDefault>assertionSource).value;
const forwardDefaultT = (<ForwardDefault>assertionSource).t;
const forwardDefaultU = (<ForwardDefault>assertionSource).u;