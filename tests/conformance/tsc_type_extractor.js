#!/usr/bin/env node
const fs = require("fs");
const path = require("path");

function parseArgs(argv) {
  const args = new Map();
  for (let i = 2; i < argv.length; i += 2) {
    const key = argv[i];
    const value = argv[i + 1];
    if (!key || !key.startsWith("--") || value === undefined) {
      throw new Error("usage: tsc_type_extractor.js --cases-root DIR --out FILE [--repo-root DIR]");
    }
    args.set(key.slice(2), value);
  }
  return args;
}

function loadTypeScript(repoRoot) {
  const candidates = [];
  if (process.env.TYPESCRIPT_MODULE) {
    candidates.push(process.env.TYPESCRIPT_MODULE);
  }
  candidates.push(path.join(repoRoot, "target", "conformance", "node_modules", "typescript", "lib", "typescript.js"));
  candidates.push(path.join(repoRoot, "vendor", "TypeScript", "built", "local", "typescript.js"));
  candidates.push(path.join(repoRoot, "vendor", "TypeScript", "lib", "typescript.js"));

  for (const candidate of candidates) {
    if (candidate && fs.existsSync(candidate)) {
      return require(candidate);
    }
  }

  try {
    return require("typescript");
  } catch {
    const message = [
      "Unable to load the TypeScript compiler API.",
      "Install the npm `typescript` package, build the TypeScript submodule, or set TYPESCRIPT_MODULE=/path/to/typescript.js.",
      "Tried:",
      ...candidates.map((candidate) => `  - ${candidate}`),
      `  - require("typescript") from ${process.cwd()}`,
    ].join("\n");
    throw new Error(message);
  }
}

function discoverCompilerCases(casesRoot) {
  const compilerRoot = path.join(casesRoot, "compiler");
  return fs
    .readdirSync(compilerRoot, { withFileTypes: true })
    .filter((entry) => entry.isFile() && (/\.tsx?$/.test(entry.name)))
    .map((entry) => path.join(compilerRoot, entry.name))
    .sort();
}

function sanitize(value) {
  return String(value).replace(/[\t\r\n]+/g, " ").trim();
}

function recordForNode(ts, checker, sourceFile, relativePath, node) {
  if (!ts.isIdentifier(node)) {
    return undefined;
  }

  const symbol = checker.getSymbolAtLocation(node);
  if (!symbol) {
    return undefined;
  }

  const start = node.getStart(sourceFile, false);
  const end = node.getEnd();
  const text = sanitize(node.getText(sourceFile));
  const type = checker.getTypeOfSymbolAtLocation(symbol, node);
  const typeText = sanitize(checker.typeToString(type, node));
  return `${relativePath}\t${start}\t${end}\t${text}\t${typeText}`;
}

function collectRecords(ts, checker, sourceFile, relativePath) {
  const records = [];
  const stack = [sourceFile];
  while (stack.length > 0) {
    const node = stack.pop();
    const record = recordForNode(ts, checker, sourceFile, relativePath, node);
    if (record) {
      records.push(record);
    }
    const children = [];
    ts.forEachChild(node, (child) => {
      children.push(child);
    });
    for (let index = children.length - 1; index >= 0; index -= 1) {
      stack.push(children[index]);
    }
  }
  return records;
}

function main() {
  const args = parseArgs(process.argv);
  const repoRoot = path.resolve(args.get("repo-root") || process.cwd());
  const casesRoot = path.resolve(args.get("cases-root"));
  const outPath = path.resolve(args.get("out"));
  const ts = loadTypeScript(repoRoot);
  const files = discoverCompilerCases(casesRoot);
  const options = {
    allowJs: true,
    checkJs: true,
    jsx: ts.JsxEmit.Preserve,
    module: ts.ModuleKind.CommonJS,
    noEmit: true,
    skipLibCheck: true,
    strict: true,
    target: ts.ScriptTarget.Latest,
  };

  const program = ts.createProgram(files, options);
  const checker = program.getTypeChecker();
  const records = [];

  for (const sourceFile of program.getSourceFiles()) {
    const fileName = path.resolve(sourceFile.fileName);
    if (!fileName.startsWith(casesRoot + path.sep)) {
      continue;
    }
    const relativePath = path.relative(casesRoot, fileName).replace(/\\/g, "/");
    if (!relativePath.startsWith("compiler/")) {
      continue;
    }

    try {
      records.push(...collectRecords(ts, checker, sourceFile, relativePath));
    } catch (error) {
      const message = sanitize(error && error.message ? error.message : String(error));
      records.push(`${relativePath}\t0\t0\t<extractor-error>\t${message}`);
    }
  }

  for (const file of files) {
    const relativePath = path.relative(casesRoot, file).replace(/\\/g, "/");
    if (!program.getSourceFile(file)) {
      records.push(`${relativePath}\t0\t0\t<file>\t<missing source file>`);
    }
  }

  records.sort();
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, `${records.join("\n")}\n`);
}

try {
  main();
} catch (error) {
  console.error(error && error.stack ? error.stack : String(error));
  process.exit(1);
}
