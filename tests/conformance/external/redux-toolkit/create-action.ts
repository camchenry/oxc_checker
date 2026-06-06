// @target: es2022

// @filename: packages/toolkit/src/reduxImports.ts
export interface Action<T extends string = string> {
  type: T
}

export function isAction(action: unknown): action is Action {
  return typeof action === 'object' && action !== null && 'type' in action
}

// @filename: packages/toolkit/src/tsHelpers.ts
export type IsAny<T, True, False = never> = true | false extends (T extends never
  ? true
  : false)
  ? True
  : False

export type IsUnknown<T, True, False = never> = unknown extends T
  ? IsAny<T, False, True>
  : False

export type IfMaybeUndefined<P, True, False> = [undefined] extends [P]
  ? True
  : False

export type IfVoid<P, True, False> = [void] extends [P] ? True : False

export type IsEmptyObj<T, True, False = never> = T extends any
  ? keyof T extends never
    ? IsUnknown<T, False, IfMaybeUndefined<T, False, IfVoid<T, False, True>>>
    : False
  : never

export type AtLeastTS35<True, False> = [True, False][IsUnknown<
  ReturnType<<T>() => T>,
  0,
  1
>]

export type IsUnknownOrNonInferrable<T, True, False> = AtLeastTS35<
  IsUnknown<T, True, False>,
  IsEmptyObj<T, True, IsUnknown<T, True, False>>
>

export interface TypeGuard<T> {
  (value: any): value is T
}

export interface HasMatchFunction<T> {
  match: TypeGuard<T>
}

export type Matcher<T> = HasMatchFunction<T> | TypeGuard<T>

export type ActionFromMatcher<M extends Matcher<any>> = M extends Matcher<
  infer T
>
  ? T
  : never

export function hasMatchFunction<T>(value: Matcher<T>): value is HasMatchFunction<T> {
  return !!value && typeof (value as HasMatchFunction<T>).match === 'function'
}

// @filename: packages/toolkit/src/createAction.ts
import { isAction } from './reduxImports'
import type {
  IfMaybeUndefined,
  IfVoid,
  IsAny,
  IsUnknownOrNonInferrable,
} from './tsHelpers'
import { hasMatchFunction } from './tsHelpers'

export type PayloadAction<
  P = void,
  T extends string = string,
  M = never,
  E = never,
> = {
  payload: P
  type: T
} & ([M] extends [never]
  ? {}
  : {
      meta: M
    }) &
  ([E] extends [never]
    ? {}
    : {
        error: E
      })

export type PrepareAction<P> =
  | ((...args: any[]) => { payload: P })
  | ((...args: any[]) => { payload: P; meta: any })
  | ((...args: any[]) => { payload: P; error: any })
  | ((...args: any[]) => { payload: P; meta: any; error: any })

export type _ActionCreatorWithPreparedPayload<
  PA extends PrepareAction<any> | void,
  T extends string = string,
> = PA extends PrepareAction<infer P>
  ? ActionCreatorWithPreparedPayload<
      Parameters<PA>,
      P,
      T,
      ReturnType<PA> extends { error: infer E } ? E : never,
      ReturnType<PA> extends { meta: infer M } ? M : never
    >
  : void

export type BaseActionCreator<P, T extends string, M = never, E = never> = {
  type: T
  match: (action: unknown) => action is PayloadAction<P, T, M, E>
}

export interface ActionCreatorWithPreparedPayload<
  Args extends unknown[],
  P,
  T extends string = string,
  E = never,
  M = never,
> extends BaseActionCreator<P, T, M, E> {
  (...args: Args): PayloadAction<P, T, M, E>
}

export interface ActionCreatorWithOptionalPayload<P, T extends string = string>
  extends BaseActionCreator<P, T> {
  (payload?: P): PayloadAction<P, T>
}

export interface ActionCreatorWithoutPayload<T extends string = string>
  extends BaseActionCreator<undefined, T> {
  (noArgument?: void): PayloadAction<undefined, T>
}

export interface ActionCreatorWithPayload<P, T extends string = string>
  extends BaseActionCreator<P, T> {
  (payload: P): PayloadAction<P, T>
}

export interface ActionCreatorWithNonInferrablePayload<
  T extends string = string,
> extends BaseActionCreator<unknown, T> {
  <PT extends unknown>(payload: PT): PayloadAction<PT, T>
}

export type PayloadActionCreator<
  P = void,
  T extends string = string,
  PA extends PrepareAction<P> | void = void,
> = IfPrepareActionMethodProvided<
  PA,
  _ActionCreatorWithPreparedPayload<PA, T>,
  IsAny<
    P,
    ActionCreatorWithPayload<any, T>,
    IsUnknownOrNonInferrable<
      P,
      ActionCreatorWithNonInferrablePayload<T>,
      IfVoid<
        P,
        ActionCreatorWithoutPayload<T>,
        IfMaybeUndefined<
          P,
          ActionCreatorWithOptionalPayload<P, T>,
          ActionCreatorWithPayload<P, T>
        >
      >
    >
  >
>

export function createAction<P = void, T extends string = string>(
  type: T,
): PayloadActionCreator<P, T>

export function createAction<
  PA extends PrepareAction<any>,
  T extends string = string,
>(type: T, prepareAction: PA): PayloadActionCreator<ReturnType<PA>['payload'], T, PA>

export function createAction(type: string, prepareAction?: Function): any {
  function actionCreator(...args: any[]) {
    if (prepareAction) {
      const prepared = prepareAction(...args)

      return {
        type,
        payload: prepared.payload,
        ...('meta' in prepared && { meta: prepared.meta }),
        ...('error' in prepared && { error: prepared.error }),
      }
    }

    return { type, payload: args[0] }
  }

  actionCreator.type = type
  actionCreator.match = (action: unknown): action is PayloadAction =>
    isAction(action) && action.type === type

  return actionCreator
}

export function isActionCreator(
  action: unknown,
): action is BaseActionCreator<unknown, string> & Function {
  return typeof action === 'function' && 'type' in action && hasMatchFunction(action as any)
}

type IfPrepareActionMethodProvided<
  PA extends PrepareAction<any> | void,
  True,
  False,
> = PA extends (...args: any[]) => any ? True : False

// @filename: tests/create-action-usage.ts
import { createAction, isActionCreator } from '../packages/toolkit/src/createAction'
import type {
  ActionCreatorWithNonInferrablePayload,
  PayloadAction,
  PayloadActionCreator,
} from '../packages/toolkit/src/createAction'
import type { ActionFromMatcher } from '../packages/toolkit/src/tsHelpers'

export const increment = createAction<number, 'counter/increment'>('counter/increment')
export const incrementAction = increment(5)
export const incrementPayload = incrementAction.payload

export const reset = createAction('counter/reset')
export const resetAction = reset()
export const resetPayload = resetAction.payload

export const setName = createAction<string | undefined, 'user/nameChanged'>(
  'user/nameChanged',
)
export const missingNameAction = setName()
export const namedAction = setName('Ada')

export const addTodo = createAction(
  'todos/add',
  (title: string, priority = 1) => ({
    payload: { title, priority },
    meta: { createdAt: 1 },
    error: false as boolean,
  }),
)
export const preparedTodoAction = addTodo('read fixture', 2)
export const preparedPayload = preparedTodoAction.payload
export const preparedMeta = preparedTodoAction.meta
export const preparedError = preparedTodoAction.error

declare const unknownAction: unknown

if (increment.match(unknownAction)) {
  const matchedPayload = unknownAction.payload
  const matchedType = unknownAction.type
  void matchedPayload
  void matchedType
}

export type IncrementAction = ReturnType<typeof increment>
export type TodoAction = ReturnType<typeof addTodo>
export type IncrementFromMatcher = ActionFromMatcher<typeof increment>
export type UnknownCreator = PayloadActionCreator<unknown, 'unknown/value'>
export type AnythingCreator = PayloadActionCreator<any, 'anything/value'>
export type GenericCreator = ActionCreatorWithNonInferrablePayload<'generic/value'>

declare const unknownCreator: UnknownCreator
declare const anythingCreator: AnythingCreator
declare const genericCreator: GenericCreator

export const unknownValueAction = unknownCreator({ nested: true })
export const anythingValueAction = anythingCreator({ count: 1 })
export const genericValueAction = genericCreator(['a', 'b'])

export const matcherAction: IncrementFromMatcher = increment(9)
export const explicitAction: PayloadAction<number, 'counter/increment'> = incrementAction
export const creatorCheck = isActionCreator(addTodo)