// @target: es2022

// @filename: src/vanilla.ts
export type SetStateInternal<T> = {
  _(partial: T | Partial<T> | ((state: T) => T | Partial<T>), replace?: false): void
  _(state: T | ((state: T) => T), replace: true): void
}['_']

export interface StoreApi<T> {
  setState: SetStateInternal<T>
  getState: () => T
  getInitialState: () => T
  subscribe: (listener: (state: T, prevState: T) => void) => () => void
}

export type StoreMutatorIdentifier = keyof StoreMutators<unknown, unknown>

export interface StoreMutators<S, A> {}

export type Mutate<S, Ms> = number extends Ms['length' & keyof Ms]
  ? S
  : Ms extends []
    ? S
    : Ms extends [[infer Mi, infer Ma], ...infer Mrs]
      ? Mutate<StoreMutators<S, Ma>[Mi & StoreMutatorIdentifier], Mrs>
      : never

export type StateCreator<
  T,
  Mis extends [StoreMutatorIdentifier, unknown][] = [],
  Mos extends [StoreMutatorIdentifier, unknown][] = [],
  U = T,
> = ((
  setState: Get<Mutate<StoreApi<T>, Mis>, 'setState', never>,
  getState: Get<Mutate<StoreApi<T>, Mis>, 'getState', never>,
  store: Mutate<StoreApi<T>, Mis>,
) => U) & { $$storeMutators?: Mos }

type Get<T, K, F> = K extends keyof T ? T[K] : F

export type ExtractState<S> = S extends { getState: () => infer T } ? T : never

export type CreateStore = {
  <T, Mos extends [StoreMutatorIdentifier, unknown][] = []>(
    initializer: StateCreator<T, [], Mos>,
  ): Mutate<StoreApi<T>, Mos>
  <T>(): <Mos extends [StoreMutatorIdentifier, unknown][] = []>(
    initializer: StateCreator<T, [], Mos>,
  ) => Mutate<StoreApi<T>, Mos>
}

export const createStore: CreateStore = ((initializer?: StateCreator<any>) => {
  if (!initializer) {
    return (nextInitializer: StateCreator<any>) => createStore(nextInitializer)
  }
  let state: any
  const listeners = new Set<(state: any, prevState: any) => void>()
  const api: StoreApi<any> = {
    setState(partial: any) {
      const prevState = state
      state = typeof partial === 'function' ? { ...state, ...partial(state) } : { ...state, ...partial }
      listeners.forEach(listener => listener(state, prevState))
    },
    getState: () => state,
    getInitialState: () => state,
    subscribe(listener) {
      listeners.add(listener)
      return () => listeners.delete(listener)
    },
  }
  state = initializer(api.setState, api.getState, api)
  return api
}) as CreateStore

// @filename: src/react.ts
import { createStore } from './vanilla'
import type {
  ExtractState,
  Mutate,
  StateCreator,
  StoreApi,
  StoreMutatorIdentifier,
} from './vanilla'

export type ReadonlyStoreApi<T> = Pick<
  StoreApi<T>,
  'getState' | 'getInitialState' | 'subscribe'
>

export type UseBoundStore<S extends ReadonlyStoreApi<unknown>> = {
  (): ExtractState<S>
  <U>(selector: (state: ExtractState<S>) => U): U
} & S

export type Create = {
  <T, Mos extends [StoreMutatorIdentifier, unknown][] = []>(
    initializer: StateCreator<T, [], Mos>,
  ): UseBoundStore<Mutate<StoreApi<T>, Mos>>
  <T>(): <Mos extends [StoreMutatorIdentifier, unknown][] = []>(
    initializer: StateCreator<T, [], Mos>,
  ) => UseBoundStore<Mutate<StoreApi<T>, Mos>>
}

export const create: Create = ((initializer?: StateCreator<any>) => {
  if (!initializer) {
    return (nextInitializer: StateCreator<any>) => create(nextInitializer)
  }
  const api = createStore(initializer)
  function useBoundStore(selector?: (state: any) => any) {
    return selector ? selector(api.getState()) : api.getState()
  }
  return Object.assign(useBoundStore, api)
}) as Create

// @filename: tests/store-api-usage.ts
import { create } from '../src/react'
import type { ExtractState, StateCreator, StoreApi } from '../src/vanilla'

type CounterState = {
  count: number
  label?: string
  increment: (by?: number) => void
}

const counterInitializer: StateCreator<CounterState> = (set, get) => ({
  count: 0,
  increment: (by = 1) => set({ count: get().count + by }),
})

const useCounter = create(counterInitializer)

type CounterFromHook = ExtractState<typeof useCounter>
type CounterStore = StoreApi<CounterState>

const current = useCounter()
const count = useCounter(state => state.count)
const increment = useCounter(state => state.increment)
const unsubscribe = useCounter.subscribe((state, prevState) => {
  const nextCount = state.count
  const prevCount = prevState.count
  nextCount + prevCount
})

const explicitState: CounterFromHook = current
const api: CounterStore = useCounter
useCounter.setState({ label: 'ready' })
increment(2)
unsubscribe()