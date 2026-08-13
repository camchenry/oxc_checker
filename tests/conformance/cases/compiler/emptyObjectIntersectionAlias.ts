// @target: es2022

type DefinedString = (string | null | undefined) & {};

interface Container {
  value: DefinedString;
}

declare const container: Container;
const _value = container.value;