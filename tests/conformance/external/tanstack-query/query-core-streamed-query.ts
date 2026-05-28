// @target: es2022

// @filename: packages/query-core/src/types.ts
export interface Register {
  // queryKey: ReadonlyArray<unknown>
}

export type QueryKey = Register extends {
  queryKey: infer TQueryKey
}
  ? TQueryKey extends ReadonlyArray<unknown>
    ? TQueryKey
    : TQueryKey extends Array<unknown>
      ? TQueryKey
      : ReadonlyArray<unknown>
  : ReadonlyArray<unknown>

export declare const dataTagSymbol: unique symbol
export type dataTagSymbol = typeof dataTagSymbol
export declare const dataTagErrorSymbol: unique symbol
export type dataTagErrorSymbol = typeof dataTagErrorSymbol
export declare const unsetMarker: unique symbol
export type UnsetMarker = typeof unsetMarker

export type AnyDataTag = {
  [dataTagSymbol]: any
  [dataTagErrorSymbol]: any
}

export type DataTag<TType, TValue, TError = UnsetMarker> = TType extends AnyDataTag
  ? TType
  : TType & {
      [dataTagSymbol]: TValue
      [dataTagErrorSymbol]: TError
    }

export type InferDataFromTag<TQueryFnData, TTaggedQueryKey extends QueryKey> =
  TTaggedQueryKey extends DataTag<unknown, infer TaggedValue, unknown>
    ? TaggedValue
    : TQueryFnData

export interface QueryClient {
  getQueryData<TData>(queryKey: QueryKey): TData | undefined
  setQueryData<TData>(
    queryKey: QueryKey,
    updater: TData | ((previous: TData | undefined) => TData),
  ): void
}

export type QueryMeta = Register extends {
  queryMeta: infer TQueryMeta
}
  ? TQueryMeta extends Record<string, unknown>
    ? TQueryMeta
    : Record<string, unknown>
  : Record<string, unknown>

export type FetchDirection = 'forward' | 'backward'

export type QueryFunctionContext<
  TQueryKey extends QueryKey = QueryKey,
  TPageParam = never,
> = [TPageParam] extends [never]
  ? {
      client: QueryClient
      queryKey: TQueryKey
      signal: AbortSignal
      meta: QueryMeta | undefined
      pageParam?: unknown
      direction?: unknown
    }
  : {
      client: QueryClient
      queryKey: TQueryKey
      signal: AbortSignal
      pageParam: TPageParam
      direction: FetchDirection
      meta: QueryMeta | undefined
    }

export type QueryFunction<
  T = unknown,
  TQueryKey extends QueryKey = QueryKey,
  TPageParam = never,
> = (context: QueryFunctionContext<TQueryKey, TPageParam>) => T | Promise<T>

export interface InfiniteData<TData, TPageParam = unknown> {
  pages: Array<TData>
  pageParams: Array<TPageParam>
}

export type OmitKeyof<
  TObject,
  TKey extends TStrictly extends 'safely'
    ? keyof TObject | (string & Record<never, never>)
    : keyof TObject,
  TStrictly extends 'strictly' | 'safely' = 'strictly',
> = Omit<TObject, TKey>

// @filename: packages/query-core/src/streamedQuery.ts
import type {
  OmitKeyof,
  QueryFunction,
  QueryFunctionContext,
  QueryKey,
} from './types'

type BaseStreamedQueryParams<TQueryFnData, TQueryKey extends QueryKey> = {
  streamFn: (
    context: QueryFunctionContext<TQueryKey>,
  ) => AsyncIterable<TQueryFnData> | Promise<AsyncIterable<TQueryFnData>>
  refetchMode?: 'append' | 'reset' | 'replace'
}

type SimpleStreamedQueryParams<
  TQueryFnData,
  TQueryKey extends QueryKey,
> = BaseStreamedQueryParams<TQueryFnData, TQueryKey> & {
  reducer?: never
  initialValue?: never
}

type ReducibleStreamedQueryParams<
  TQueryFnData,
  TData,
  TQueryKey extends QueryKey,
> = BaseStreamedQueryParams<TQueryFnData, TQueryKey> & {
  reducer: (acc: TData, chunk: TQueryFnData) => TData
  initialValue: TData
}

type StreamedQueryParams<
  TQueryFnData,
  TData,
  TQueryKey extends QueryKey,
> =
  | SimpleStreamedQueryParams<TQueryFnData, TQueryKey>
  | ReducibleStreamedQueryParams<TQueryFnData, TData, TQueryKey>

export function streamedQuery<
  TQueryFnData = unknown,
  TData = Array<TQueryFnData>,
  TQueryKey extends QueryKey = QueryKey,
>({
  streamFn,
  refetchMode = 'reset',
  reducer = (items, chunk) => [...(items as Array<TQueryFnData>), chunk] as TData,
  initialValue = [] as TData,
}: StreamedQueryParams<TQueryFnData, TData, TQueryKey>): QueryFunction<
  TData,
  TQueryKey
> {
  return async (context) => {
    const signalLessContext: OmitKeyof<typeof context, 'signal'> = {
      client: context.client,
      meta: context.meta,
      queryKey: context.queryKey,
      pageParam: context.pageParam,
      direction: context.direction,
    }
    const stream = await streamFn(signalLessContext as QueryFunctionContext<TQueryKey>)
    let result = initialValue

    for await (const chunk of stream) {
      if (refetchMode === 'replace') {
        result = reducer(result, chunk)
      } else {
        context.client.setQueryData<TData>(context.queryKey, (previous) =>
          reducer(previous === undefined ? initialValue : previous, chunk),
        )
      }
    }

    return context.client.getQueryData<TData>(context.queryKey) ?? result
  }
}

// @filename: tests/query-core-usage.ts
import { streamedQuery } from '../packages/query-core/src/streamedQuery'
import type {
  DataTag,
  InferDataFromTag,
  InfiniteData,
  QueryFunctionContext,
} from '../packages/query-core/src/types'

type Todo = {
  id: number
  title: string
}

type TodoQueryKey = DataTag<readonly ['todos'], Todo[], Error>
type TaggedTodoData = InferDataFromTag<string, TodoQueryKey>

declare const todoStream: AsyncIterable<Todo>
declare const context: QueryFunctionContext<readonly ['todos'], number>

const pageParam = context.pageParam
const queryFn = streamedQuery<Todo, InfiniteData<Todo, number>, readonly ['todos']>({
  streamFn: () => todoStream,
  reducer: (data, todo) => ({
    pages: [...data.pages, todo],
    pageParams: [...data.pageParams, pageParam],
  }),
  initialValue: { pages: [], pageParams: [] },
  refetchMode: 'append',
})

const taggedData: TaggedTodoData = [{ id: 1, title: 'read fixture' }]
const queryResult = queryFn(context)
