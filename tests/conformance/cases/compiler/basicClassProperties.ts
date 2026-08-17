// @target: es2022
class ClassPropertyItem {
  name: string = "item";
}

class ClassPropertyExample {
  ready: boolean = false;
  count = 1;
  item: ClassPropertyItem = new ClassPropertyItem();
  static enabled: boolean = true;

  getReady() {
    return this.ready;
  }

  getCount() {
    return this.count;
  }

  getItemName() {
    return this.item.name;
  }

  static getEnabled() {
    return ClassPropertyExample.enabled;
  }
}

const _classPropertyInstance = new ClassPropertyExample();
const _classPropertyReady = _classPropertyInstance.ready;
const _classPropertyCount = _classPropertyInstance.count;
const _classPropertyItemName = _classPropertyInstance.item.name;
const _classPropertyReadyFromThis = _classPropertyInstance.getReady();
const _classPropertyCountFromThis = _classPropertyInstance.getCount();
const _classPropertyNameFromThis = _classPropertyInstance.getItemName();
const _classPropertyEnabled = ClassPropertyExample.enabled;
const _classPropertyEnabledFromMethod = ClassPropertyExample.getEnabled();
const _classPropertyPrototype = ClassPropertyExample.prototype;
const _classPropertyPrototypeReady = ClassPropertyExample.prototype.ready;
const _ClassPropertyConstructor = ClassPropertyExample;
const _classPropertyAliasedEnabled = _ClassPropertyConstructor.enabled;
const _classPropertyAliasedInstance = new _ClassPropertyConstructor();