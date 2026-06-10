// @filename: a.ts
String('123');
'123'.toString();
'' + '123';
'123' + '';

Number(123);
+123;
~~123;

Boolean(true);
!!true;

BigInt(BigInt(1));

let str = '123';
str += '';

// @filename: b.ts
function foo(bar: string | number) {
  String(bar);
  bar.toString();
  '' + bar;
  bar + '';

  Number(bar);
  +bar;
  ~~bar;

  Boolean(bar);
  !!bar;

  BigInt(1);

  bar += '';
}