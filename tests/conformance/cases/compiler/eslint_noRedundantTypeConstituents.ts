// @filename: a.ts
type UnionAny = any | 'foo';
type UnionUnknown = unknown | 'foo';
type UnionNever = never | 'foo';

type UnionBooleanLiteral = boolean | false;
type UnionNumberLiteral = number | 1;
type UnionStringLiteral = string | 'foo';

type IntersectionAny = any & 'foo';
type IntersectionUnknown = string & unknown;
type IntersectionNever = string | never;

type IntersectionBooleanLiteral = boolean & false;
type IntersectionNumberLiteral = number & 1;
type IntersectionStringLiteral = string & 'foo';

// @filename: b.ts
type UnionAny = any;
type UnionUnknown = unknown;
type UnionNever = never;

type UnionBooleanLiteral = boolean;
type UnionNumberLiteral = number;
type UnionStringLiteral = string;

type IntersectionAny = any;
type IntersectionUnknown = string;
type IntersectionNever = string;

type IntersectionBooleanLiteral = false;
type IntersectionNumberLiteral = 1;
type IntersectionStringLiteral = 'foo';