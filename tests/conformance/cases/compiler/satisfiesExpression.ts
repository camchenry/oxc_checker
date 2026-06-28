const x: number = 1 satisfies 2 | 3
const y = 1 satisfies 2 | 3

// Test `satisfies` expression in more contexts and edge cases
type Point = { x: number; y: number }
type Named = { name: string }
type Handler<T> = (value: T) => T
type Status = "idle" | "loading" | "done"
type StringNumberRecord = { [key: string]: number }
type StatusMap = { idle: number; loading: number; done: number }

const literalNumber = 1 satisfies number
const literalString = "hello" satisfies string
const literalBoolean = true satisfies boolean
const literalUnion = "idle" satisfies Status
const literalTemplate = `id-${literalNumber}` satisfies `id-${number}`

const tuple = [1, "two"] satisfies [number, string]
const readonlyTuple = [1, 2, 3] as const satisfies readonly number[]
const array = ["red", "green", "blue"] satisfies string[]
const nestedArray = [[1], [2, 3]] satisfies number[][]

const point = { x: 0, y: 1 } satisfies Point
const namedPoint = { name: "origin", x: 0, y: 0 } satisfies Named & Point
const optionalShape = { x: 1 } satisfies { x: number; y?: number }
const recordShape = { a: 1, b: 2 } satisfies StringNumberRecord
const literalRecord = { idle: 0, loading: 1, done: 2 } satisfies StatusMap

const nestedObject = {
	id: "root",
	child: { x: 1, y: 2 },
} satisfies { id: string; child: Point }

const methodObject = {
	scale(value: number) {
		return value * 2
	},
} satisfies { scale(value: number): number }

const arrow = ((value: number) => value + 1) satisfies Handler<number>
const genericArrow = (<T>(value: T) => value) satisfies <T>(value: T) => T
const constructorLike = class {
	value = 1
} satisfies new () => { value: number }

const parenthesized = (1 + 2) satisfies number
const conditional = (literalBoolean ? "yes" : "no") satisfies "yes" | "no"
const nullish = (undefined ?? "fallback") satisfies string
const chained = ({ x: 1, y: 2 } satisfies Point).x satisfies number

declare const maybePoint: Point | undefined
const narrowed = maybePoint?.x satisfies number | undefined

declare function takesPoint<T extends Point>(value: T): T
const genericCall = takesPoint({ x: 1, y: 2 }) satisfies Point

const missingProperty = { x: 1 } satisfies Point
const wrongPropertyType = { x: 1, y: "two" } satisfies Point
const excessProperty = { x: 1, y: 2, z: 3 } satisfies Point
const wrongTuple = [1, 2] satisfies [number, string]
const wrongFunction = ((value: string) => value) satisfies Handler<number>
