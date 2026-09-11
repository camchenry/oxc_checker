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