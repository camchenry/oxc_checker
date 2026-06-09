// @target: es2022

// @filename: src/internal/types.ts
export type EnumerableStringKeyedValueOf<T> = T extends readonly (infer Item)[]
  ? Item
  : T extends object
    ? T[keyof T & string]
    : never

export type NonEmptyArray<T> = readonly [T, ...T[]]

export type LazyEvaluator<T, R> = (value: T, index: number, data: readonly T[]) => R

export type Pred<T> = LazyEvaluator<T, boolean>

export type Merge<ObjectType> = { [Key in keyof ObjectType]: ObjectType[Key] } & {}

// @filename: src/map.ts
import type { EnumerableStringKeyedValueOf, LazyEvaluator } from './internal/types'

export function map<T, U>(data: readonly T[], callbackfn: LazyEvaluator<T, U>): U[]
export function map<T extends object, U>(
  data: T,
  callbackfn: LazyEvaluator<EnumerableStringKeyedValueOf<T>, U>,
): U[]
export function map(data: unknown, callbackfn: LazyEvaluator<any, any>): any[] {
  return Array.isArray(data)
    ? data.map((value, index) => callbackfn(value, index, data))
    : Object.values(data as object).map((value, index, values) => callbackfn(value, index, values))
}

// @filename: src/filter.ts
import type { Pred } from './internal/types'

export function filter<T, S extends T>(
  data: readonly T[],
  predicate: (value: T, index: number, data: readonly T[]) => value is S,
): S[]
export function filter<T>(data: readonly T[], predicate: Pred<T>): T[]
export function filter(data: readonly unknown[], predicate: Pred<any>): unknown[] {
  return data.filter((value, index) => predicate(value, index, data))
}

// @filename: src/groupBy.ts
export function groupBy<T, Key extends PropertyKey>(
  data: readonly T[],
  callbackfn: (value: T, index: number, data: readonly T[]) => Key,
): Partial<Record<Key, T[]>> {
  const out: Partial<Record<Key, T[]>> = {}
  for (let index = 0; index < data.length; index++) {
    const value = data[index]
    const key = callbackfn(value, index, data)
    ;(out[key] ??= []).push(value)
  }
  return out
}

// @filename: src/pick.ts
import type { Merge, NonEmptyArray } from './internal/types'

export function pick<T extends object, Keys extends keyof T>(
  data: T,
  keys: NonEmptyArray<Keys>,
): Merge<Pick<T, Keys>> {
  const out = {} as Pick<T, Keys>
  for (const key of keys) {
    out[key] = data[key]
  }
  return out
}

// @filename: src/pipe.ts
export function pipe<A>(value: A): A
export function pipe<A, B>(value: A, op1: (input: A) => B): B
export function pipe<A, B, C>(value: A, op1: (input: A) => B, op2: (input: B) => C): C
export function pipe<A, B, C, D>(
  value: A,
  op1: (input: A) => B,
  op2: (input: B) => C,
  op3: (input: C) => D,
): D
export function pipe(value: unknown, ...operations: Array<(input: any) => any>): unknown {
  return operations.reduce((current, operation) => operation(current), value)
}

// @filename: tests/data-first-usage.ts
import { filter } from '../src/filter'
import { groupBy } from '../src/groupBy'
import { map } from '../src/map'
import { pick } from '../src/pick'
import { pipe } from '../src/pipe'

type Task = {
  id: string
  status: 'todo' | 'done'
  points?: number
}

const tasks: Task[] = [
  { id: 'a', status: 'todo' },
  { id: 'b', status: 'done', points: 3 },
]

const doneTasks = filter(
  tasks,
  (task): task is Task & { status: 'done'; points: number } => task.status === 'done',
)
const donePoints = map(doneTasks, task => task.points)
const groupedTasks = groupBy(tasks, task => task.status)
const taskSummary = pick(tasks[1], ['id', 'points'])
const pointTotal = pipe(
  doneTasks,
  items => map(items, item => item.points),
  points => points.reduce((sum, point) => sum + point, 0),
)

const groupedDone = groupedTasks.done
const summaryId = taskSummary.id
const summaryPoints = taskSummary.points
const firstPoint = donePoints[0]