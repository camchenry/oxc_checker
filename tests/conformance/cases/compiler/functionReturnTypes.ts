// @target: es2022

function empty() {

}

function emptyVoid(): void {
  
}

class EmptyGetter {
  public get x() {

  }
}

function returnsBig() {
  return 1n
}

function returnsBig2() {
  if (1 + 1 === 4) {
    return 0n;
  }
  return 1n
}