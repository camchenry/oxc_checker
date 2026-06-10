// @filename: a.ts
void (() => {})();

function foo() {}
void foo();

// @filename: b.ts
(() => {})();

function foo() {}
foo(); // nothing to discard

function bar(x: number) {
  void x; // discarding a number
  return 2;
}
void bar(1); // discarding a number