// @filename: a.ts
function foo(): undefined {}
function bar(flag: boolean): undefined {
  if (flag) return foo();
  return;
}

async function baz(flag: boolean): Promise<undefined> {
  if (flag) return;
  return foo();
}

// @filename: b.ts
function foo(): void {}
function bar(flag: boolean): void {
  if (flag) return foo();
  return;
}

async function baz(flag: boolean): Promise<void | number> {
  if (flag) return 42;
  return;
}