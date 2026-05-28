// @target: es2022
// @allowImportingTsExtensions: true

// @filename: a.ts
function process<T>(x: T) {
  if (x) {
    return 1;
  }
  return x;
}
const mod = { process };
export { process };
export default mod;

// @filename: index.ts
import { process } from './a.ts'

const num: number = 5
const str: string = "foo"

const i1_num = process(num)
const i1_str = process(str)

import modDefault from './a.ts'

const i2_num = modDefault.process(num)
const i2_str = modDefault.process(str)

import * as modNamespace from './a.ts'

const i3_num = modNamespace.process(num)
const i3_str = modNamespace.process(str)