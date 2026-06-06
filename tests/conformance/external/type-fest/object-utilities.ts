// @target: es2022

// @filename: source/internal/index.ts
export type ApplyDefaultOptions<
  Options extends object,
  Defaults extends Required<Options>,
  SpecifiedOptions extends Options,
> = {
  [Key in keyof Defaults]: Key extends keyof SpecifiedOptions
    ? NonNullable<SpecifiedOptions[Key & keyof SpecifiedOptions]>
    : Defaults[Key]
}

export type HomomorphicPick<BaseType, Keys extends keyof BaseType> = {
  [Key in Keys]: BaseType[Key]
}

// @filename: source/is-equal.ts
export type IsEqual<A, B> = (<G>() => G extends A ? 1 : 2) extends <G>() =>
  G extends B ? 1 : 2
  ? true
  : false

// @filename: source/simplify.ts
export type Simplify<T> = { [KeyType in keyof T]: T[KeyType] } & {}

// @filename: source/except.ts
import type { ApplyDefaultOptions } from './internal/index'
import type { IsEqual } from './is-equal'

type Filter<KeyType, ExcludeType> = IsEqual<KeyType, ExcludeType> extends true
  ? never
  : KeyType extends ExcludeType
    ? never
    : KeyType

export type ExceptOptions = {
  requireExactProps?: boolean
}

type DefaultExceptOptions = {
  requireExactProps: false
}

export type Except<
  ObjectType,
  KeysType extends keyof ObjectType,
  Options extends ExceptOptions = {},
> = _Except<
  ObjectType,
  KeysType,
  ApplyDefaultOptions<ExceptOptions, DefaultExceptOptions, Options>
>

type _Except<
  ObjectType,
  KeysType extends keyof ObjectType,
  Options extends Required<ExceptOptions>,
> = {
  [KeyType in keyof ObjectType as Filter<KeyType, KeysType>]: ObjectType[KeyType]
} & (Options['requireExactProps'] extends true
  ? Partial<Record<KeysType, never>>
  : {})

// @filename: source/set-required.ts
import type { Except } from './except'
import type { HomomorphicPick } from './internal/index'
import type { Simplify } from './simplify'

export type SetRequired<BaseType, Keys extends keyof BaseType> = Simplify<
  Except<BaseType, Keys> & Required<HomomorphicPick<BaseType, Keys>>
>

// @filename: source/union-to-intersection.ts
export type UnionToIntersection<Union> = (
  Union extends unknown ? (distributedUnion: Union) => void : never
) extends (mergedIntersection: infer Intersection) => void
  ? Intersection & Union
  : never

// @filename: source/keys-of-union.ts
import type { UnionToIntersection } from './union-to-intersection'

export type KeysOfUnion<ObjectType> = keyof UnionToIntersection<
  ObjectType extends unknown ? Record<keyof ObjectType, never> : never
>

// @filename: tests/object-utilities-usage.ts
import type { Except } from '../source/except'
import type { KeysOfUnion } from '../source/keys-of-union'
import type { SetRequired } from '../source/set-required'
import type { Simplify } from '../source/simplify'

type User = {
  id: string
  name?: string
  email?: string
  profile: {
    avatarUrl?: string
    flags: string[]
  }
}

type PublicUser = Except<User, 'email'>
type StrictPublicUser = Except<User, 'email', { requireExactProps: true }>
type ContactableUser = SetRequired<User, 'name' | 'email'>
type UserPreview = Simplify<
  Except<ContactableUser, 'profile'> & { displayName: string }
>

type CreatedEvent = {
  type: 'created'
  user: User
}

type DeletedEvent = {
  type: 'deleted'
  id: string
  actor?: string
}

type Event = CreatedEvent | DeletedEvent
type EventKey = KeysOfUnion<Event>

const publicUser: PublicUser = {
  id: 'user-1',
  name: 'Ada',
  profile: {
    flags: ['admin'],
  },
}

const strictPublicUser: StrictPublicUser = {
  id: 'user-2',
  profile: {
    avatarUrl: '/avatars/user-2.png',
    flags: [],
  },
}

const contactableUser: ContactableUser = {
  id: 'user-3',
  name: 'Grace',
  email: 'grace@example.com',
  profile: {
    flags: ['beta'],
  },
}

const userPreview: UserPreview = {
  id: 'user-4',
  name: 'Lin',
  email: 'lin@example.com',
  displayName: 'Lin H.',
}

const eventKey: EventKey = 'actor'
const omittedEmail = strictPublicUser.email