// @filename: a.ts
const arg1 = [1, 2];
const msg1 = `arg1 = ${arg1}`;

const arg2 = { name: 'Foo' };
const msg2 = `arg2 = ${arg2 || null}`;

// @filename: b.ts
const arg = 'foo';
const msg1 = `arg = ${arg}`;
const msg2 = `arg = ${arg || 'default'}`;

const stringWithKindProp: string & { _kind?: 'MyString' } = 'foo';
const msg3 = `stringWithKindProp = ${stringWithKindProp}`;

// @filename: c.ts
const arg = 123;
const msg1 = `arg = ${arg}`;
const msg2 = `arg = ${arg || 'zero'}`;

// @filename: d.ts
const arg = true;
const msg1 = `arg = ${arg}`;
const msg2 = `arg = ${arg || 'not truthy'}`;

// @filename: e.ts
const user = JSON.parse('{ "name": "foo" }');
const msg1 = `arg = ${user.name}`;
const msg2 = `arg = ${user.name || 'the user with no name'}`;

// @filename: f.ts
const arg = condition ? 'ok' : null;
const msg1 = `arg = ${arg}`;

// @filename: g.ts
const arg = new RegExp('foo');
const msg1 = `arg = ${arg}`;

// @filename: h.ts
const arg = /foo/;
const msg1 = `arg = ${arg}`;

// @filename: i.ts
const arg = 'something';
const msg1 = typeof arg === 'string' ? arg : `arg = ${arg}`;

// @filename: j.ts
const arg = ['foo', 'bar'];
const msg1 = `arg = ${arg}`;