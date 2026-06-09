// @target: es2022

// @filename: src/v3/types.ts
export type input<T extends ZodTypeAny> = T['_input']
export type output<T extends ZodTypeAny> = T['_output']

export abstract class ZodType<Output = any, Input = Output> {
  readonly _output!: Output
  readonly _input!: Input
  abstract parse(data: unknown): Output
  optional(): ZodOptional<this> {
    return new ZodOptional(this)
  }
  array(): ZodArray<this> {
    return new ZodArray(this)
  }
}

export type ZodTypeAny = ZodType<any, any>

export class ZodString extends ZodType<string> {
  parse(data: unknown): string {
    return String(data)
  }
}

export class ZodNumber extends ZodType<number> {
  parse(data: unknown): number {
    return Number(data)
  }
}

export class ZodBoolean extends ZodType<boolean> {
  parse(data: unknown): boolean {
    return Boolean(data)
  }
}

export class ZodOptional<T extends ZodTypeAny> extends ZodType<
  output<T> | undefined,
  input<T> | undefined
> {
  constructor(readonly innerType: T) {
    super()
  }
  parse(data: unknown): output<T> | undefined {
    return data === undefined ? undefined : this.innerType.parse(data)
  }
}

export class ZodArray<T extends ZodTypeAny> extends ZodType<output<T>[], input<T>[]> {
  constructor(readonly element: T) {
    super()
  }
  parse(data: unknown): output<T>[] {
    return (data as unknown[]).map(value => this.element.parse(value))
  }
}

export type ZodRawShape = Record<string, ZodTypeAny>

export type objectOutputType<Shape extends ZodRawShape> = {
  [Key in keyof Shape]: output<Shape[Key]>
}

export type objectInputType<Shape extends ZodRawShape> = {
  [Key in keyof Shape]: input<Shape[Key]>
}

export class ZodObject<Shape extends ZodRawShape> extends ZodType<
  objectOutputType<Shape>,
  objectInputType<Shape>
> {
  constructor(readonly shape: Shape) {
    super()
  }
  parse(data: unknown): objectOutputType<Shape> {
    const out: Record<string, unknown> = {}
    for (const key in this.shape) {
      out[key] = this.shape[key].parse((data as Record<string, unknown>)[key])
    }
    return out as objectOutputType<Shape>
  }
  pick<Mask extends { [Key in keyof Shape]?: true }>(
    mask: Mask,
  ): ZodObject<Pick<Shape, keyof Mask & keyof Shape>> {
    const out = {} as Pick<Shape, keyof Mask & keyof Shape>
    for (const key in mask) {
      out[key as keyof Mask & keyof Shape] = this.shape[key as keyof Shape]
    }
    return new ZodObject(out)
  }
}

// @filename: src/v3/external.ts
import { ZodBoolean, ZodNumber, ZodObject, ZodString } from './types'
import type { ZodRawShape } from './types'

export const z = {
  string: () => new ZodString(),
  number: () => new ZodNumber(),
  boolean: () => new ZodBoolean(),
  object: <Shape extends ZodRawShape>(shape: Shape) => new ZodObject(shape),
}

// @filename: tests/object-inference-usage.ts
import { z } from '../src/v3/external'
import type { input, output } from '../src/v3/types'

const accountSchema = z.object({
  id: z.string(),
  email: z.string().optional(),
  scores: z.number().array(),
  active: z.boolean(),
})

const publicAccountSchema = accountSchema.pick({ id: true, active: true })

type AccountInput = input<typeof accountSchema>
type AccountOutput = output<typeof accountSchema>
type PublicAccount = output<typeof publicAccountSchema>

const inputValue: AccountInput = {
  id: 'account-1',
  email: undefined,
  scores: [1, 2],
  active: true,
}

const parsedAccount = accountSchema.parse(inputValue)
const explicitAccount: AccountOutput = parsedAccount
const publicAccount: PublicAccount = publicAccountSchema.parse(parsedAccount)
const score = parsedAccount.scores[0]
const publicActive = publicAccount.active