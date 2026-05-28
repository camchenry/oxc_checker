// @target: es2022

// @filename: sources/Any/Key.ts
export type Key = string | number | symbol

// @filename: sources/Object/_Internal.ts
export type Depth = 'flat' | 'deep'

// @filename: sources/Any/Equals.ts
export type Equals<A1 extends any, A2 extends any> =
  (<A>() => A extends A2 ? 1 : 0) extends (<A>() => A extends A1 ? 1 : 0)
    ? 1
    : 0

// @filename: sources/Object/Pick.ts
import type { Key } from '../Any/Key'

export type Pick<O extends object, K extends Key> = {
  [P in keyof O as P extends K ? P : never]: O[P]
} & {}

// @filename: sources/Object/Patch.ts
export type PatchFlat<O extends object, O1 extends object> = {
  [K in keyof (O & O1)]: K extends keyof O
    ? O[K]
    : K extends keyof O1
      ? O1[K]
      : never
} & {}

// @filename: sources/Object/Optional.ts
import type { Pick } from './Pick'
import type { Depth } from './_Internal'
import type { Key } from '../Any/Key'
import type { PatchFlat } from './Patch'
import type { Equals } from '../Any/Equals'

export type OptionalFlat<O> = {
  [K in keyof O]?: O[K]
} & {}

export type OptionalDeep<O> = {
  [K in keyof O]?: OptionalDeep<O[K]>
}

export type OptionalPart<O extends object, depth extends Depth> = {
  flat: OptionalFlat<O>
  deep: OptionalDeep<O>
}[depth]

export type Optional<
  O extends object,
  K extends Key = Key,
  depth extends Depth = 'flat',
> = {
  1: OptionalPart<O, depth>
  0: PatchFlat<OptionalPart<Pick<O, K>, depth>, O>
}[Equals<Key, K>]

// @filename: tests/object-optional-usage.ts
import type {
  Optional,
  OptionalDeep,
  OptionalFlat,
} from '../sources/Object/Optional'

type User = {
  id: string
  name: string
  profile: {
    email: string
    address: {
      city: string
    }
  }
}

type OptionalName = Optional<User, 'name'>
type OptionalEverything = Optional<User>
type OptionalProfileDeep = Optional<User, 'profile', 'deep'>
type DirectFlat = OptionalFlat<User>
type DirectDeep = OptionalDeep<User>

const optionalName: OptionalName = {
  id: 'user-1',
  profile: {
    email: 'user@example.com',
    address: {
      city: 'Berlin',
    },
  },
}

const optionalEverything: OptionalEverything = {}
const optionalProfileDeep: OptionalProfileDeep = {
  id: 'user-2',
  name: 'Ada',
  profile: {
    address: {},
  },
}

const directFlat: DirectFlat = {
  id: 'user-3',
}
const directDeep: DirectDeep = {
  profile: {
    address: {},
  },
}
