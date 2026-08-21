// @filename: classProperties.ts
export {};
class Item {
  name: string = "item";
}
class Example {
  ready: boolean = false;
  count = 1;
  item: Item = new Item();
  static enabled: boolean = true;
  getReady() { return this.ready; }
  getCount() { return this.count; }
  getItemName() { return this.item.name; }
  static getEnabled() { return Example.enabled; }
}
const instance = new Example();
const ready = instance.ready;
const count = instance.count;
const itemName = instance.item.name;
const readyFromThis = instance.getReady();
const countFromThis = instance.getCount();
const nameFromThis = instance.getItemName();
const enabled = Example.enabled;
const enabledFromMethod = Example.getEnabled();

// @filename: every.ts
export {};
class Ship { isSunk: boolean = false; }
class Board {
  ships: Ship[] = [];
  allShipsSunk() {
    return this.ships.every(function (value) { return value.isSunk; });
  }
}
const board = new Board();
const sunk = board.allShipsSunk();

// @filename: asyncMap.ts
export {};
const mapped = [1, 2, 3].map(async value => value + 1);

// @filename: stringMap.ts
export {};
const lengths = ["a", "bb", "ccc"].map(value => value.length);

// @filename: destructuredClass.ts
export {};
abstract class DestructuredBase {
  abstract value: string;
  constructor() {
    const { value: renamed } = this;
  }
}