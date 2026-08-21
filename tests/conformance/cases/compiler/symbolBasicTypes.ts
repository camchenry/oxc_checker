const declaredNumber: number = 1;
const declaredString: string = "hello";
const declaredBoolean: boolean = true;
const declaredBigint: bigint = 1n;
const declaredUndefined: undefined = undefined;
const declaredNull: null = null;
const declaredAny: any = 1;
const declaredUnknown: unknown = 1;

const arrayCtor = Array;
const promiseCtor = Promise;
const mapCtor = Map;
const setCtor = Set;
const symbolCtor = Symbol;
const objectCtor = Object;
const objectKeys = Object.keys({ a: 1 });
const constructedArray = new Array<number>(1);

const declaredArray: number[] = [1, 2, 3];
const genericArray: Array<number> = [1, 2, 3];
const readonlyArray: ReadonlyArray<string> = ["a"];

let tuple: [number, string];
let tupleNumber = tuple[0];
let tupleString = tuple[1];
let tupleMissing = tuple[2];

declare const stringIndex: { [key: string]: bigint };
const stringIndexValue = stringIndex.anything;

const literalCount = 1;
const literalLabel = "ready";
const quotedLabel = '\"ready\"';
const quoteOnlyNot = !'\"\"';
const literalEnabled = true;
const widenedSum = literalCount + 2;
const widenedMessage = literalLabel + "!";

let inferredBoolean = false;
let inferredNumber = 23;
let inferredString = "hello";
let inferredBigint = 1n;
let inferredAny;
let mismatchedAnnotation: string = 23;