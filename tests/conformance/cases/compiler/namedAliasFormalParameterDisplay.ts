type Lazy<T, R> = () => R;
type Pred<T> = Lazy<T, boolean>;
declare function filter<T>(predicate: Pred<T>): void;