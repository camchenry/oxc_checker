// @target: es2022

// @filename: library/types.ts
export type BaseIssue<Expected extends string = string> = {
  readonly kind: 'schema'
  readonly expected: Expected
  readonly message: string
}

export type BaseSchema<Input, Output, Issue extends BaseIssue> = {
  readonly '~types'?: {
    readonly input: Input
    readonly output: Output
    readonly issue: Issue
  }
  readonly '~run': (input: unknown) => Output
}

export type GenericSchema = BaseSchema<any, any, BaseIssue>

export type InferInput<TSchema extends GenericSchema> = NonNullable<
  TSchema['~types']
>['input']

export type InferOutput<TSchema extends GenericSchema> = NonNullable<
  TSchema['~types']
>['output']

export type InferIssue<TSchema extends GenericSchema> = NonNullable<
  TSchema['~types']
>['issue']

// @filename: library/schemas.ts
import type {
  BaseIssue,
  BaseSchema,
  GenericSchema,
  InferInput,
  InferIssue,
  InferOutput,
} from './types'

export type StringSchema = BaseSchema<string, string, BaseIssue<'string'>>
export type NumberSchema = BaseSchema<number, number, BaseIssue<'number'>>
export type BooleanSchema = BaseSchema<boolean, boolean, BaseIssue<'boolean'>>

export type OptionalSchema<TWrapped extends GenericSchema, TDefault = undefined> = BaseSchema<
  InferInput<TWrapped> | undefined,
  InferOutput<TWrapped> | TDefault,
  InferIssue<TWrapped>
>

export type ArraySchema<TItem extends GenericSchema> = BaseSchema<
  InferInput<TItem>[],
  InferOutput<TItem>[],
  InferIssue<TItem>
>

export type ObjectEntries = Record<string, GenericSchema>

export type ObjectInput<TEntries extends ObjectEntries> = {
  [Key in keyof TEntries]: InferInput<TEntries[Key]>
}

export type ObjectOutput<TEntries extends ObjectEntries> = {
  [Key in keyof TEntries]: InferOutput<TEntries[Key]>
}

export type ObjectIssue<TEntries extends ObjectEntries> = {
  [Key in keyof TEntries]: InferIssue<TEntries[Key]>
}[keyof TEntries]

export type ObjectSchema<TEntries extends ObjectEntries> = BaseSchema<
  ObjectInput<TEntries>,
  ObjectOutput<TEntries>,
  ObjectIssue<TEntries>
>

export function string(): StringSchema {
  return { '~run': input => String(input) }
}

export function number(): NumberSchema {
  return { '~run': input => Number(input) }
}

export function boolean(): BooleanSchema {
  return { '~run': input => Boolean(input) }
}

export function optional<TWrapped extends GenericSchema, TDefault = undefined>(
  wrapped: TWrapped,
  default_: TDefault,
): OptionalSchema<TWrapped, TDefault> {
  return { '~run': input => (input === undefined ? default_ : wrapped['~run'](input)) as any }
}

export function array<TItem extends GenericSchema>(item: TItem): ArraySchema<TItem> {
  return { '~run': input => (input as unknown[]).map(value => item['~run'](value)) }
}

export function object<TEntries extends ObjectEntries>(
  entries: TEntries,
): ObjectSchema<TEntries> {
  return {
    '~run': input => {
      const out: Record<string, unknown> = {}
      for (const key in entries) {
        out[key] = entries[key]['~run']((input as Record<string, unknown>)[key])
      }
      return out as ObjectOutput<TEntries>
    },
  }
}

// @filename: tests/schema-output-usage.ts
import { array, boolean, number, object, optional, string } from '../library/schemas'
import type { InferInput, InferIssue, InferOutput } from '../library/types'

const userSchema = object({
  id: string(),
  age: optional(number(), 0),
  active: boolean(),
  tags: array(string()),
})

type UserInput = InferInput<typeof userSchema>
type UserOutput = InferOutput<typeof userSchema>
type UserIssue = InferIssue<typeof userSchema>

const input: UserInput = {
  id: 'user-1',
  age: undefined,
  active: true,
  tags: ['admin'],
}

const output = userSchema['~run'](input)
const explicitOutput: UserOutput = output
const userAge = output.age
const userTags = output.tags
const issue: UserIssue = {
  kind: 'schema',
  expected: 'string',
  message: 'Invalid string',
}