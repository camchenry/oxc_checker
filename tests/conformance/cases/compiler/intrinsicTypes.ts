type Upper = Uppercase<"hello world">;
type Lower = Lowercase<"HELLO WORLD">;
type Capital = Capitalize<"hello world">;
type Uncapital = Uncapitalize<"Hello world">;

type UpperUnion = Uppercase<"hello" | "World">;
type LowerTemplate = Lowercase<`HTTP/${"GET" | "POST"}`>;
type CapitalTemplate = Capitalize<`hello-${string}`>;
type UncapitalTemplate = Uncapitalize<`Hello-${string}`>;

type DeferredUpper<T extends string> = Uppercase<T>;
type NoInferValue = NoInfer<"value">;