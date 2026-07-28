// @target: es2022

class BrandedValue {
  #brand = true;
  #secret = 1;

  static hasBrand(value: object): boolean {
    const result = #brand in value;
    return result && new BrandedValue().#brand;
  }

  hasSecret(value: object): boolean {
    const result = #secret in value;
    return result && this.#secret > 0;
  }
}

const _staticResult = BrandedValue.hasBrand({});
const _instanceResult = new BrandedValue().hasSecret({});