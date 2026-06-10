// @filename: a.ts
enum Status {
  Unknown,
  Closed = 1,
  Open = 'open',
}

enum Status2 {
  Unknown = 0,
  Closed = 1,
  Open = 2,
}

enum Status3 {
  Unknown,
  Closed,
  Open,
}

enum Status4 {
  Unknown = 'unknown',
  Closed = 'closed',
  Open = 'open',
}

// @filename: b.ts
enum Status {
  Closed = 'closed',
  Open = 'open',
}

// ['closed', 'open']
Object.values(Status);

// @filename: c.ts
enum Status {
  Unknown,
  Closed = 1,
  Open = 'open',
}

// ["Unknown", "Closed", 0, 1, "open"]
Object.values(Status);