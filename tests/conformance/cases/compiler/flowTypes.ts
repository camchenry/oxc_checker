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