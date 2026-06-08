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
  console.log(maybeAction);
  // string
  console.log(maybeAction.type);
}

if (typeof maybeAction === "object" && maybeAction !== null && "type" in maybeAction) {
  // object & Record<"type", unknown>
  console.log(maybeAction);
  // unknown
  console.log(maybeAction.type);
}
