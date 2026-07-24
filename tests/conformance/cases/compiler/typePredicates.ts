type IsString = (value: unknown) => value is string;
type AssertString = (value: unknown) => asserts value is string;
type AssertValue = (value: unknown) => asserts value;
type ThisIsReady = (this: { ready: boolean }) => this is { ready: true };

interface PredicateArray<T> {
    every<S extends T>(predicate: (value: T, index: number, array: readonly T[]) => value is S): this is readonly S[];
}

interface MethodSignatureCoverage<T> {
    narrow<U extends T>(this: MethodSignatureCoverage<T>, value: U): value is U;
    overload(value: string): string;
    overload(value: number): number;
}

declare const methodSignatures: MethodSignatureCoverage<string>;

const _narrow = methodSignatures.narrow("value");
const _stringOverload = methodSignatures.overload("value");
const _numberOverload = methodSignatures.overload(1);
