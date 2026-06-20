class A {
  [key: string]: string;
}

interface B {
  [key: string]: string;
}

type C = {
  [key: string]: string;
};

type Multi = {
  [key: string, key2: number]: object;
}

type Multi2 = {
  [key: string]: string;
  [key2: number]: string;
  [key3: symbol]: string;
}