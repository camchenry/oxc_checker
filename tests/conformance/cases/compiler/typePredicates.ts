type IsString = (value: unknown) => value is string;
type AssertString = (value: unknown) => asserts value is string;
type AssertValue = (value: unknown) => asserts value;
type ThisIsReady = (this: { ready: boolean }) => this is { ready: true };

interface PredicateArray<T> {
    every<S extends T>(predicate: (value: T, index: number, array: readonly T[]) => value is S): this is readonly S[];
}
