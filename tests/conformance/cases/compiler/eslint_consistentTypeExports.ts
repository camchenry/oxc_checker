// @filename: a.ts
interface ButtonProps {
  onClick: () => void;
}

class Button implements ButtonProps {
  onClick = () => console.log('button!');
}

export { Button, ButtonProps };

// @filename: b.ts
interface ButtonProps {
  onClick: () => void;
}

class Button implements ButtonProps {
  onClick = () => console.log('button!');
}

export { Button };
export type { ButtonProps };

// @filename: c.ts
const x = 1;
type T = number;

export { x, T };

// @filename: d.ts
const x = 1;
type T = number;

export { x, type T };

// @filename: e.ts
const x = 1;
type T = number;

export type { T };
export { x };