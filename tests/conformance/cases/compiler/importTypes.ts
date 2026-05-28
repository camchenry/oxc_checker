// @target: es2022

// @filename: a.ts
function process<T>(x: T) {
  if (x) {
    return 1;
  }
  return x;
}

// @filename: index.ts
import { process } from './a.ts'

const i1_num = process(5)
const i1_str = process("foo")

import mod from './a.ts'

const i2_num = mod.process(5)
const i2_str = mod.process("foo")

import * as mod from './a.ts'

const i3_num = mod.process(5)
const i3_str = mod.process("foo")