type User = {
  name: string;
  age: number;
  id: `user_${string}`
  active?: boolean;
  address: {
    city: string;
    zip: number;
  };
  greet(message: string): string;
  preferences: {
    theme: "light" | "dark";
    notifications?: boolean;
  };
}

const user: User = {
  name: "Alice",
  age: 30,
  id: "user_Alice",
  address: {
    city: "Paris",
    zip: 75000,
  },
  greet(message: string) {
    return `${message}, ${this.name}`;
  },
  preferences: {
    theme: "dark",
  },
};

const userName = user.name;
const userAge = user.age;
const userId = user.id;
const userActive = user.active;
const userCity = user.address.city;
const userZip = user["address"].zip;
const userGreeting = user.greet("hello");
const userGreetMethod = user.greet;
const userTheme = user.preferences.theme;
const userNotifications = user.preferences.notifications;

const literalKey = "name" as const;
const unionKey: "name" | "id" = Math.random() > 0.5 ? "name" : "id";
const dynamicStringKey: string = "whatever";

const literalKeyValue = user[literalKey];
const unionKeyValue = user[unionKey];
const dynamicStringKeyValue = user[dynamicStringKey];

type StringDictionary = {
  known: number;
  [key: string]: number;
}

const dictionary: StringDictionary = {
  known: 1,
  extra: 2,
};

const dictionaryKnownDot = dictionary.known;
const dictionaryKnownBracket = dictionary["known"];
const dictionaryExtraDot = dictionary.extra;
const dictionaryDynamic = dictionary[dynamicStringKey];

type NumericDictionary = {
  0: "zero";
  1?: "one";
  [index: number]: "zero" | "one" | "many" | undefined;
}

const numericDictionary: NumericDictionary = {
  0: "zero",
  2: "many",
};

const numericZeroDot = numericDictionary[0];
const numericOneBracket = numericDictionary[1];
const numericDynamic = numericDictionary[42];

const users = [user, { ...user, name: "Bob", id: "user_Bob" }] as const;
const firstUser = users[0];
const firstUserName = users[0].name;
const usersLength = users.length;
const arrayMapMethod = users.map;

const tuple = ["ready", 200, { ok: true }] as const;
const tupleStatus = tuple[0];
const tupleCode = tuple[1];
const tupleObjectOk = tuple[2].ok;
const tupleLength = tuple.length;
const tupleBracketLength = tuple["length"];

declare const optionalTuple: readonly [string, number?];
const optionalTupleLength = optionalTuple.length;
const optionalTupleBracketLength = optionalTuple["length"];

declare const restTuple: readonly [string, ...number[]];
const restTupleLength = restTuple.length;
const restTupleBracketLength = restTuple["length"];

const matrix = [[1, 2], [3, 4]] as const;
const matrixFirstRow = matrix[0];
const matrixFirstValue = matrix[0][0];

type CallableWithProperty = {
  (value: number): string;
  description: string;
}

declare const callableWithProperty: CallableWithProperty;
const callableResult = callableWithProperty(123);
const callableDescription = callableWithProperty.description;
const callableApply = callableWithProperty.apply;

class Counter {
  static label = "counter";
  static create() {
    return new Counter(0);
  }

  #secret = 10;

  constructor(public value: number) {}

  increment() {
    this.value += 1;
    return this.value;
  }

  readSecret() {
    return this.#secret;
  }
}

const counter = new Counter(1);
const counterValue = counter.value;
const counterIncrement = counter.increment;
const counterIncrementResult = counter.increment();
const counterSecret = counter.readSecret();
const counterStaticLabel = Counter.label;
const counterStaticFactory = Counter.create;
const counterStaticResult = Counter.create();

class DerivedCounter extends Counter {
  readSuperIncrement() {
    return super.increment();
  }
}

const derived = new DerivedCounter(5);
const derivedSuperResult = derived.readSuperIncrement();

const uniqueKey: unique symbol = Symbol("uniqueKey");
type SymbolObject = {
  [uniqueKey]: number;
  regular: string;
}

const symbolObject: SymbolObject = {
  [uniqueKey]: 42,
  regular: "ok",
};

const symbolValue = symbolObject[uniqueKey];
const symbolRegular = symbolObject.regular;

type Hyphenated = {
  "data-id": string;
  "aria-label"?: string;
}

const hyphenated: Hyphenated = {
  "data-id": "item-1",
};

const hyphenatedDataId = hyphenated["data-id"];
const hyphenatedAriaLabel = hyphenated["aria-label"];

type UnionMember =
  | { kind: "text"; value: string; common: boolean }
  | { kind: "count"; value: number; common: boolean }

declare const unionMember: UnionMember;
const unionKind = unionMember.kind;
const unionValue = unionMember.value;
const unionCommon = unionMember.common;

type IntersectionMember = { left: string } & { right: number };
declare const intersectionMember: IntersectionMember;
const intersectionLeft = intersectionMember.left;
const intersectionRight = intersectionMember.right;

const parenthesizedMember = (user).name;
const assertedMember = (user as User).age;
const satisfiesMember = ({ value: 1 } satisfies { value: number }).value;
