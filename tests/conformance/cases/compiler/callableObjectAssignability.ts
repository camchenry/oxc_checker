// @strictNullChecks: true

// @filename: overloads.ts
declare let single: () => number;
declare let overloaded: {
    (): number;
    (value: string): number;
};

single = overloaded;
overloaded = single;

// @filename: requiredProperty.ts
declare let plainFunction: () => number;
declare let callableWithProperty: {
    (): number;
    required: string;
};

plainFunction = callableWithProperty;
callableWithProperty = plainFunction;

// @filename: nonCallable.ts
declare let callable: () => number;
declare let nonCallable: {};

callable = nonCallable;
nonCallable = callable;

// @filename: weakTarget.ts
declare let weakSource: () => number;
declare let weakTarget: { localeMatcher?: string };

weakTarget = weakSource;
weakSource = weakTarget;

// @filename: constructOnly.ts
declare let callOnly: () => {};
declare let constructOnly: new () => {};

callOnly = constructOnly;
constructOnly = callOnly;

// @filename: signatureDisplay.ts
declare let singleCallObject: { (value: string): number };
declare let singleConstructObject: { new(value: string): {} };
declare let overloadedConstructObject: {
    new(): {};
    new(value: string): {};
};
declare let constructWithProperty: { new(): {}; tag: boolean };
declare let callAndConstruct: { (): number; new(): {} };
declare let constructorSyntax: new () => {};
declare let abstractConstructorSyntax: abstract new () => {};
declare let callObjectArray: { (): number }[];
declare let constructObjectArray: { new(): {} }[];
declare let takesConstructObject: (ctor: { new(): {} }) => void;
declare let returnsCallObject: () => { (): number };
declare let takesCallObjectArray: (callbacks: { (): number }[]) => void;
declare let objectWithSignatureTypes: {
    call: { (): number };
    construct: { new(): {} };
    calls: { (): number }[];
    constructs: { new(): {} }[];
};
type ConstructorAlias = { new(): {} };
declare let constructorAlias: ConstructorAlias;
