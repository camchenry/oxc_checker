// @target: es2022

// @filename: src/types/utils.ts
export type Primitive = null | undefined | string | number | boolean | symbol | bigint

export type BrowserNativeObject = Date | FileList | File

export type IsAny<T> = 0 extends 1 & T ? true : false

export type IsTuple<T extends ReadonlyArray<any>> = number extends T['length']
  ? false
  : true

export type TupleKeys<T extends ReadonlyArray<any>> = Exclude<keyof T, keyof any[]>

export type ArrayKey = number

export type AnyIsEqual<T1, T2> = T1 extends T2
  ? (<G>() => G extends T1 ? 1 : 2) extends <G>() => G extends T2 ? 1 : 2
    ? true
    : never
  : never

// @filename: src/types/path/eager.ts
import type {
  AnyIsEqual,
  ArrayKey,
  BrowserNativeObject,
  IsAny,
  IsTuple,
  Primitive,
  TupleKeys,
} from '../utils'

type PathImpl<K extends string | number, V, TraversedTypes> = V extends
  | Primitive
  | BrowserNativeObject
  ? `${K}`
  : true extends AnyIsEqual<TraversedTypes, V>
    ? `${K}`
    : `${K}` | `${K}.${PathInternal<V, TraversedTypes | V>}`

type PathInternal<T, TraversedTypes = T> = T extends ReadonlyArray<infer V>
  ? IsTuple<T> extends true
    ? {
        [K in TupleKeys<T>]-?: PathImpl<K & string, T[K], TraversedTypes>
      }[TupleKeys<T>]
    : PathImpl<ArrayKey, V, TraversedTypes>
  : {
      [K in keyof T]-?: PathImpl<K & string, T[K], TraversedTypes>
    }[keyof T]

export type Path<T> = T extends any ? PathInternal<T> : never
export type FieldPath<TFieldValues> = Path<TFieldValues>

type PathValue<T, P extends Path<T> | ArrayPath<T>> = T extends any
  ? P extends `${infer K}.${infer R}`
    ? K extends keyof T
      ? R extends Path<T[K]>
        ? PathValue<T[K], R>
        : never
      : K extends `${ArrayKey}`
        ? T extends ReadonlyArray<infer V>
          ? PathValue<V, R & Path<V>>
          : never
        : never
    : P extends keyof T
      ? T[P]
      : P extends `${ArrayKey}`
        ? T extends ReadonlyArray<infer V>
          ? V
          : never
        : never
  : never

type ArrayPathImpl<K extends string | number, V, TraversedTypes> = V extends
  | Primitive
  | BrowserNativeObject
  ? never
  : V extends ReadonlyArray<infer U>
    ? U extends Primitive | BrowserNativeObject
      ? never
      : true extends AnyIsEqual<TraversedTypes, V>
        ? never
        : `${K}` | `${K}.${ArrayPathInternal<V, TraversedTypes | V>}`
    : true extends AnyIsEqual<TraversedTypes, V>
      ? never
      : `${K}.${ArrayPathInternal<V, TraversedTypes | V>}`

type ArrayPathInternal<T, TraversedTypes = T> = T extends ReadonlyArray<infer V>
  ? IsAny<T> extends true
    ? string
    : IsTuple<T> extends true
      ? {
          [K in TupleKeys<T>]-?: ArrayPathImpl<K & string, T[K], TraversedTypes>
        }[TupleKeys<T>]
      : ArrayPathImpl<ArrayKey, V, TraversedTypes>
  : {
      [K in keyof T]-?: ArrayPathImpl<K & string, T[K], TraversedTypes>
    }[keyof T]

export type ArrayPath<T> = T extends any ? ArrayPathInternal<T> : never
export type FieldArrayPath<TFieldValues> = ArrayPath<TFieldValues>
export type FieldPathValue<
  TFieldValues,
  TFieldPath extends FieldPath<TFieldValues>,
> = PathValue<TFieldValues, TFieldPath>

export type FieldArrayPathValue<
  TFieldValues,
  TFieldArrayPath extends FieldArrayPath<TFieldValues>,
> = PathValue<TFieldValues, TFieldArrayPath>

// @filename: tests/field-path-usage.ts
import type {
  FieldArrayPath,
  FieldArrayPathValue,
  FieldPath,
  FieldPathValue,
} from '../src/types/path/eager'

type ContactForm = {
  user: {
    name: string
    address: {
      city: string
      zip?: number
    }
  }
  tags: string[]
  friends: Array<{
    name: string
    socials: [{ kind: 'email'; value: string }, { kind: 'phone'; value: number }]
  }>
}

type ContactField = FieldPath<ContactForm>
type ContactArrayField = FieldArrayPath<ContactForm>
type CityValue = FieldPathValue<ContactForm, 'user.address.city'>
type FriendValue = FieldArrayPathValue<ContactForm, 'friends'>
type SocialValue = FieldPathValue<ContactForm, 'friends.0.socials.1.value'>

const field: ContactField = 'friends.0.socials.1.value'
const arrayField: ContactArrayField = 'friends.0.socials'
const city: CityValue = 'Paris'
const friend: FriendValue = {
  name: 'Ada',
  socials: [
    { kind: 'email', value: 'a@example.test' },
    { kind: 'phone', value: 1 },
  ],
}
const social: SocialValue = 123