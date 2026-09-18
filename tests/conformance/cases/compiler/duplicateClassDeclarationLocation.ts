class C<T = number> {}
class D extends C {}
class D extends C<string> {}

class Empty {}
class WithStatic {
	static value = 0;
}
class WithInstance {
	value = 0;
}

declare const staticConstructor: { new(): {}; value: number };
export {};