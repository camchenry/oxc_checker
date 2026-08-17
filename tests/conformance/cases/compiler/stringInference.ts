type User = {
  name: string
  address: {
    city: string
  }
}
type UserKeys = keyof User

type Tupleify<T extends string> = T extends `${infer K}.${infer R}` ? [K, ...Tupleify<R>] : [T]

type Tuple1 = Tupleify<"test">
type Tuple2 = Tupleify<"test.property">
type Tuple3 = Tupleify<"test.property.another">
type Tuple4 = Tupleify<".property.another">

type T0 = "user" extends `${infer K}` ? K : never
type T1 = "user.name" extends `${infer K}.${infer R}` ? true : false
type T2 = "user.name" extends `${infer K}.${infer R}` ? R extends UserKeys ? Pick<User, R> : never : never
type T3 = Tupleify<"user.address.city"> extends [infer P1, infer P2, infer P3]
  ? P2 extends UserKeys
    ? P3 extends keyof User[P2]
      ? Pick<User[P2], P3>
      : never
    : never
  : never