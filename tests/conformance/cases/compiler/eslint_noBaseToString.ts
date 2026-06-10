// @filename: a.ts
// Passing an object or class instance to string concatenation:
'' + {};

class MyClass {}
const value = new MyClass();
value + '';

// Interpolation and manual .toString() and `toLocaleString()` calls too:
`Value: ${value}`;
String({});
({}).toString();
({}).toLocaleString();

// Stringifying objects or instances in an array with the `Array.prototype.join`.
[{}, new MyClass()].join('');

// @filename: b.ts
// These types all have useful .toString() and `toLocaleString()` methods
'Text' + true;
`Value: ${123}`;
`Arrays too: ${[1, 2, 3]}`;
(() => {}).toString();
String(42);
(() => {}).toLocaleString();

// Defining a custom .toString class is considered acceptable
class CustomToString {
  toString() {
    return 'Hello, world!';
  }
}
`Value: ${new CustomToString()}`;

const literalWithToString = {
  toString: () => 'Hello, world!',
};

`Value: ${literalWithToString}`;

// @filename: c.ts
`${/regex/}`;
'' + /regex/;
/regex/.toString();
let value = /regex/;
value.toString();
let text = `${value}`;
String(/regex/);

// @filename: d.ts
declare const x: unknown;
String(x);