interface Shape {
  hash: HashWrapper;
}
interface HashAlgorithm {}
type HashTarget = HashAlgorithm | string;
type HashWrapper = HashTarget;