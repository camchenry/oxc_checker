function f6<T extends string | (new () => {})>(a: T) {
  if (typeof a !== "string") {
    new a();
  }
}

var x13:{ new(): number; new(n:number):number; x: string; w: {y: number;}; (): {}; } = 3;
