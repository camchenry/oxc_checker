// @target: es2022
// @module: esnext

export const moduleMeta = import.meta;
export const moduleMetaUrl = import.meta.url;

class Base {
  constructor() {
    const baseTarget = new.target;
    const baseArrowTarget = () => new.target;
  }

  method() {
    const methodTarget = new.target;
  }

}

function functionTarget() {
  const target = new.target;
  const arrowTarget = () => new.target;
}
