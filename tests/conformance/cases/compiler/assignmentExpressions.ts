let x: any = 5;
const x1 = x = 5;
const x2 = x += 1;
const x3 = x += "hello"
const x4 = x -= 1;
const x5 = x *= 2;
const x6 = x /= 2;
const x7 = x %= 2;
const x8 = x |= 1;
const x9 = x ^= 1;
const x10 = x &= 1;
const x11 = x >>= 1;
const x12 = x <<= 1;
const x13 = x >>= 1;
const x14 = x >>>= 1;
const x15 = x **= 2;

let y: string | undefined | null = "test"
const x16 = y ??= "foo"
const x17 = y ??= undefined
const x18 = y &&= "foo"
const x19 = y &&= undefined
const x20 = y ||= "foo"
const x21 = y ||= undefined
