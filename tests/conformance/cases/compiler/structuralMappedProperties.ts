type Source = {
  name: string;
  count: number;
};

declare const optionalCopy: Partial<Source>;
const optionalName = optionalCopy.name;
const optionalCount = optionalCopy.count;

declare const recorded: Record<"value", string>;
const recordedValue = recorded.value;

type Boxed<Value> = Value extends string ? { value: Value } : { value: number };
declare const boxed: Boxed<"ready">;
const conditionalValue = boxed.value;