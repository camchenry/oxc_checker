declare const x: string | undefined;

if (x) {
  // string
  console.log(x);
} else {
  // string | undefined
  console.log(x);
}

declare const y: string | number | boolean;

// z: string | undefined
const z = typeof y === "string" ? y : undefined;

if (typeof y === "string") {
  // string
  console.log(y);
} else {
  // number | boolean
  console.log(y)
}

// andResult: string | undefined
const andResult = x && x;

// orResult: string
const orResult = x || "fallback";

// coalesceResult: string
const coalesceResult = x ?? "fallback";

if (x && typeof y === "string") {
  // string
  console.log(x);
  // string
  console.log(y);
}

interface Action {
  type: string;
}

declare function isAction(action: unknown): action is Action;
declare const maybeAction: unknown;

if (isAction(maybeAction) && maybeAction.type) {
  // Action
  maybeAction;
  // string
  maybeAction.type;
}

if (typeof maybeAction === "object" && maybeAction !== null && "type" in maybeAction) {
  // object & Record<"type", unknown>
  maybeAction;
  // unknown
  maybeAction.type;
}

interface GenericAction<T extends string = string> {
  type: T;
}

declare function isGenericAction(value: unknown): value is GenericAction;
declare const unknownAction: unknown;

if (isGenericAction(unknownAction)) {
  console.log(unknownAction);
}

declare const nullableValue: string | null;
const whenNull = null === nullableValue ? nullableValue : "";
const whenString = null !== nullableValue ? nullableValue : "";

function flowDirectAssignment() {
  let value: string | number;
  value = 1;
  console.log(value);
}

function flowSelfReferentialAssignment() {
  let value: number | undefined;
  value = +value;
  console.log(value);
}

let compoundWriteValue: any = 0;
compoundWriteValue = 1;
compoundWriteValue += 2;

declare const nestedBranchValue: string | number | undefined;
if (nestedBranchValue) {
  if (typeof nestedBranchValue === "string") {
    console.log(nestedBranchValue);
  }
}

let siblingBranchValue: string | undefined;
declare const siblingCondition: boolean;
if (siblingCondition && siblingBranchValue) {
  console.log(siblingBranchValue);
} else {
  siblingBranchValue = undefined;
}

declare const optionalContainer: { value: string | undefined };
if (optionalContainer?.value) {
  console.log(optionalContainer.value);
}

function evolvingSiblingBranch() {
  let values = [];
  declare const condition: boolean;
  if (condition) {
    values.push(1);
  } else {
    const untouched = values;
    console.log(untouched);
  }
}
