// @filename: a.ts
function f<T = number>() {}
f<number>();

// @filename: b.ts
function g<T = number, U = string>() {}
g<string, string>();

// @filename: c.ts
class C<T = number> {}
new C<number>();

class D extends C<number> {}

// @filename: d.ts
interface I<T = number> {}
class Impl implements I<number> {}

// @filename: e.ts
function f<T = number>() {}
f();
f<string>();

// @filename: f.ts
function g<T = number, U = string>() {}
g<string>();
g<number, number>();

// @filename: g.ts
class C<T = number> {}
new C();
new C<string>();

class D extends C {}
class D extends C<string> {}

// @filename: h.ts
interface I<T = number> {}
class Impl implements I<string> {}