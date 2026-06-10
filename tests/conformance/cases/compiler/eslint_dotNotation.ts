// @filename: a.ts
class X {
  private priv_prop = 123;
}

const x = new X();
x['priv_prop'] = 123;

// @filename: b.ts
class X {
  protected protected_prop = 123;
}

const x = new X();
x['protected_prop'] = 123;

// @filename: c.ts
class X {
  [key: string]: number;
}

const x = new X();
x['hello'] = 123;