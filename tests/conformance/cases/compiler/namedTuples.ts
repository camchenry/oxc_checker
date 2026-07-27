// @target: es2022

type Point = [x: number, y: number];
const point: Point = [10, 20];

type OptionalPoint = [x: number, y?: number];
const pointWithX: OptionalPoint = [10];
const pointWithY: OptionalPoint = [10, 20];

type Command = [name: string, ...args: string[]];
const command: Command = ["build", "--watch", "--verbose"];

type ReadonlyPoint = readonly [x: number, y: number];
const readonlyPoint: ReadonlyPoint = [10, 20];

type MessageTuple = [kind: "message", payload: string];
type ErrorTuple = [kind: "error", message: string];
type TupleEvent = MessageTuple | ErrorTuple;
declare const messageEvent: TupleEvent;
declare const errorEvent: TupleEvent;

type NestedPoint = [name: string, position: Point];
const nestedPoint: NestedPoint = ["origin", point];

declare function emit(...event: TupleEvent): void;
emit(...messageEvent);
emit(...errorEvent);