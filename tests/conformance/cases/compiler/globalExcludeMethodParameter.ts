interface Shape {
  method(format: Exclude<KeyFormat, "jwk">): void;
}