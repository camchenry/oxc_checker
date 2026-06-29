type Profile = {
	name: string
	age?: number
	greet?: (message: string) => string
	tags?: string[]
	nested?: {
		count: number
		getCount?: () => number
		values?: Array<{ label: string }>
	}
}

type Service = {
	getUser?: (id: string) => Profile | undefined
	users?: Profile[]
}

declare const maybeUser: Profile | undefined
declare const definiteUser: Profile
declare const maybeUsers: Profile[] | undefined
declare const dictionary: Record<string, Profile | undefined> | undefined
declare const handlers: Record<string, ((value: number) => string) | undefined> | undefined
declare const callback: ((value: number) => string) | undefined
declare const service: Service
declare const maybeService: Service | undefined
declare const getFactory: (() => { user?: Profile; service?: Service }) | undefined
declare const key: string
declare const index: number

const optionalName = maybeUser?.name
const optionalAge = maybeUser?.age
const optionalMethodCall = maybeUser?.greet?.("hello")
const optionalNestedProperty = maybeUser?.nested?.count
const optionalNestedMethod = maybeUser?.nested?.getCount?.()
const optionalNestedArray = maybeUser?.nested?.values?.[index]
const optionalNestedArrayLabel = maybeUser?.nested?.values?.[index]?.label

const optionalElement = maybeUser?.tags?.[0]
const optionalArrayElement = maybeUsers?.[index]
const optionalArrayElementName = maybeUsers?.[index]?.name
const optionalArrayElementMethod = maybeUsers?.[index]?.greet?.("hello")

const optionalDictionaryLookup = dictionary?.[key]
const optionalDictionaryName = dictionary?.[key]?.name
const optionalHandler = handlers?.[key]
const optionalHandlerCall = handlers?.[key]?.(123)

const optionalCall = callback?.(1)
const optionalCallProperty = callback?.(1)?.length
const optionalServiceCall = service.getUser?.("primary")
const optionalServiceCallName = service.getUser?.("primary")?.name
const optionalMaybeServiceCall = maybeService?.getUser?.("secondary")
const optionalMaybeServiceCallName = maybeService?.getUser?.("secondary")?.name

const optionalFactoryCall = getFactory?.()
const optionalFactoryUser = getFactory?.().user
const optionalFactoryUserName = getFactory?.().user?.name
const optionalFactoryServiceUser = getFactory?.().service?.getUser?.("factory")

const optionalWithNonNull = maybeUser?.nested!.count
const optionalNonNullMethod = maybeUser?.nested!.getCount?.()
const optionalGrouped = (maybeUser?.nested)?.count
const optionalGroupedCall = (maybeUser?.greet)?.("grouped")

const optionalNullish = maybeUser?.name ?? "anonymous"
const optionalLogical = maybeUser?.age && maybeUser.age.toFixed()
const optionalConditional = maybeUser?.name ? maybeUser.name : "missing"
const optionalTemplate = `user-${maybeUser?.name}`

const definiteOptionalProperty = definiteUser.tags?.[0]
const definiteOptionalMethod = definiteUser.greet?.("definite")
const definiteNestedOptionalMethod = definiteUser.nested?.getCount?.()

const optionalSatisfies = maybeUser?.name satisfies string | undefined
const optionalAs = maybeUser?.age as number | undefined
