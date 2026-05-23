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

function parseCompilerDirective(line) {
  const match = /^\/\/\s*@(\w+)\s*:\s*([^\r\n]*)/.exec(line.trimStart());
  if (!match) {
    return undefined;
  }
  return {
    key: match[1],
    normalizedKey: match[1].toLowerCase(),
    value: match[2].trim(),
  };
}

function parseCompilerCase(file, casesRoot) {
  const sourceText = fs.readFileSync(file, "utf8");
  const relativePath = path.relative(casesRoot, file).replace(/\\/g, "/");
  const settings = new Map();
  const files = [];
  let currentFileName;
  let currentFileOptions = new Map();
  let currentFileLines = [];
  let hasExplicitFiles = false;

  const lines = sourceText.split(/\r\n?|\n/);
  if (/\r\n?$|\n$/.test(sourceText)) {
    lines.pop();
  }

  for (const line of lines) {
    const directive = parseCompilerDirective(line);
    if (directive) {
      if (directive.normalizedKey === "filename") {
        hasExplicitFiles = true;
        if (currentFileName !== undefined) {
          pushCompilerFile(files, currentFileName, currentFileLines, currentFileOptions);
          currentFileLines = [];
          currentFileOptions = new Map();
        } else {
          currentFileLines = [];
        }
        currentFileName = directive.value;
      } else if (currentFileName !== undefined) {
        currentFileOptions.set(directive.key, directive.value);
      } else {
        settings.set(directive.key, directive.value);
      }
      continue;
    }

    currentFileLines.push(line);
  }

  pushCompilerFile(
    files,
    currentFileName === undefined ? path.basename(file) : currentFileName,
    currentFileLines,
    currentFileOptions,
  );

  return { physicalPath: file, relativePath, settings, files, hasExplicitFiles };
}

function pushCompilerFile(files, name, lines, options) {
  files.push({
    name: normalizeSlashes(name),
    content: lines.join("\n"),
    options,
  });
}

function normalizeSlashes(value) {
  return String(value).replace(/\\/g, "/");
}

function recordPathForFile(compilerCase, sourceFile) {
  return compilerCase.hasExplicitFiles
    ? `${compilerCase.relativePath}::${sourceFile.name}`
    : compilerCase.relativePath;
}

function optionEntries(settings) {
  return Array.from(settings, ([key, value]) => ({ key, value }));
}

function createCompilerOptions(ts, compilerCase, repoRoot) {
  const baseOptions = {
    allowJs: true,
    checkJs: true,
    jsx: ts.JsxEmit.Preserve,
    module: ts.ModuleKind.CommonJS,
    noEmit: true,
    skipLibCheck: true,
    strict: true,
    target: ts.ScriptTarget.Latest,
  };
  const optionNameMap = new Map(ts.optionDeclarations.map((option) => [option.name.toLowerCase(), option.name]));
  const jsonOptions = {};

  for (const { key, value } of optionEntries(compilerCase.settings)) {
    const normalizedKey = key.toLowerCase();
    if (normalizedKey === "filename" || normalizedKey === "usecasesensitivefilenames") {
      continue;
    }
    const optionName = optionNameMap.get(normalizedKey);
    if (!optionName) {
      continue;
    }
    jsonOptions[optionName] = parseCompilerOptionValue(normalizedKey, value);
  }

  const converted = ts.convertCompilerOptionsFromJson(jsonOptions, repoRoot);
  return { ...baseOptions, ...converted.options, noEmit: true, skipLibCheck: true };
}

function parseCompilerOptionValue(key, value) {
  const trimmed = value.trim();
  if (/^(true|false)$/i.test(trimmed)) {
    return /^true$/i.test(trimmed);
  }
  if (key === "lib" || key === "types") {
    return trimmed.split(",").map((item) => item.trim()).filter(Boolean);
  }
  if (trimmed.includes(",")) {
    return trimmed.split(",")[0].trim();
  }
  return trimmed;
}

function useCaseSensitiveFileNames(ts, compilerCase) {
  const setting = Array.from(compilerCase.settings).find(([key]) => key.toLowerCase() === "usecasesensitivefilenames");
  if (!setting) {
    return ts.sys.useCaseSensitiveFileNames;
  }
  return /^true$/i.test(setting[1].trim());
}

function isRootedTestPath(fileName) {
  return /^[a-zA-Z]:\//.test(fileName) || fileName.startsWith("/");
}

function canBatchExplicitCase(compilerCase) {
  return compilerCase.hasExplicitFiles && compilerCase.files.every((sourceFile) => !isRootedTestPath(sourceFile.name));
}

function virtualCaseDirectory(compilerCase) {
  const caseDirectory = normalizeSlashes(path.dirname(compilerCase.physicalPath));
  const caseName = path.basename(compilerCase.physicalPath).replace(/\.[^.]+$/, "");
  return `${caseDirectory}/.conformance-virtual/${caseName}`;
}

function virtualFileName(ts, compilerCase, sourceFile, namespaceExplicitFiles) {
  if (!compilerCase.hasExplicitFiles) {
    return normalizeSlashes(path.resolve(compilerCase.physicalPath));
  }
  const caseDirectory = namespaceExplicitFiles
    ? virtualCaseDirectory(compilerCase)
    : normalizeSlashes(path.dirname(compilerCase.physicalPath));
  return normalizeSlashes(ts.getNormalizedAbsolutePath(sourceFile.name, caseDirectory));
}

function canonicalFileName(ts, fileName, useCaseSensitive) {
  const normalized = normalizeSlashes(ts.normalizePath(fileName));
  return useCaseSensitive ? normalized : normalized.toLowerCase();
}

function createVirtualCompilerHost(ts, options, virtualFiles, useCaseSensitive) {
  const defaultHost = ts.createCompilerHost(options, true);
  const filesByName = new Map();
  const directories = new Set();
  for (const file of virtualFiles) {
    filesByName.set(canonicalFileName(ts, file.fileName, useCaseSensitive), file);
    addAncestorDirectories(ts, directories, file.fileName, useCaseSensitive);
  }

  return {
    ...defaultHost,
    useCaseSensitiveFileNames: () => useCaseSensitive,
    getCanonicalFileName: (fileName) => canonicalFileName(ts, fileName, useCaseSensitive),
    getCurrentDirectory: () => normalizeSlashes(process.cwd()),
    fileExists: (fileName) => filesByName.has(canonicalFileName(ts, fileName, useCaseSensitive)) || defaultHost.fileExists(fileName),
    directoryExists: (dirName) => directories.has(canonicalFileName(ts, dirName, useCaseSensitive))
      || (defaultHost.directoryExists ? defaultHost.directoryExists(dirName) : true),
    readFile: (fileName) => {
      const file = filesByName.get(canonicalFileName(ts, fileName, useCaseSensitive));
      return file ? file.content : defaultHost.readFile(fileName);
    },
    getSourceFile: (fileName, languageVersion, onError, shouldCreateNewSourceFile) => {
      const file = filesByName.get(canonicalFileName(ts, fileName, useCaseSensitive));
      if (file) {
        return ts.createSourceFile(file.fileName, file.content, languageVersion, true);
      }
      return defaultHost.getSourceFile(fileName, languageVersion, onError, shouldCreateNewSourceFile);
    },
  };
}

function addAncestorDirectories(ts, directories, fileName, useCaseSensitive) {
  let current = normalizeSlashes(path.dirname(fileName));
  while (current && current !== ".") {
    directories.add(canonicalFileName(ts, current, useCaseSensitive));
    const parent = normalizeSlashes(path.dirname(current));
    if (parent === current) {
      break;
    }
    current = parent;
  }
}

function isCompilableRootFile(fileName) {
  return /\.(d\.ts|tsx?|jsx?|mjs|cjs|mts|cts)$/i.test(fileName);
}

function stableOptionsKey(options, useCaseSensitive) {
  const optionEntries = Object.keys(options)
    .sort()
    .map((key) => [key, options[key]]);
  return JSON.stringify({ useCaseSensitive, options: optionEntries });
}

function collectProgramRecords(ts, options, virtualFiles, useCaseSensitive, records) {
  const host = createVirtualCompilerHost(ts, options, virtualFiles, useCaseSensitive);
  const rootNames = virtualFiles
    .filter((sourceFile) => isCompilableRootFile(sourceFile.fileName))
    .map((sourceFile) => sourceFile.fileName);
  const program = ts.createProgram(rootNames, options, host);
  const checker = program.getTypeChecker();
  const virtualFilesByName = new Map(
    virtualFiles.map((sourceFile) => [canonicalFileName(ts, sourceFile.fileName, useCaseSensitive), sourceFile]),
  );

  for (const sourceFile of program.getSourceFiles()) {
    const virtualFile = virtualFilesByName.get(canonicalFileName(ts, sourceFile.fileName, useCaseSensitive));
    if (!virtualFile) {
      continue;
    }

    try {
      records.push(...collectRecords(ts, checker, sourceFile, virtualFile.recordPath));
    } catch (error) {
      const message = sanitize(error && error.message ? error.message : String(error));
      records.push(`${virtualFile.recordPath}\t0\t0\t<extractor-error>\t${message}`);
    }
  }

  for (const sourceFile of virtualFiles) {
    if (isCompilableRootFile(sourceFile.fileName) && !program.getSourceFile(sourceFile.fileName)) {
      records.push(`${sourceFile.recordPath}\t0\t0\t<file>\t<missing source file>`);
    }
  }
}

function prepareCompilerCase(ts, compilerCase, repoRoot, namespaceExplicitFiles = false) {
  const options = createCompilerOptions(ts, compilerCase, repoRoot);
  const useCaseSensitive = useCaseSensitiveFileNames(ts, compilerCase);
  const virtualFiles = compilerCase.files.map((sourceFile) => ({
    ...sourceFile,
    fileName: virtualFileName(ts, compilerCase, sourceFile, namespaceExplicitFiles),
    recordPath: recordPathForFile(compilerCase, sourceFile),
  }));
  return { compilerCase, options, useCaseSensitive, virtualFiles };
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
  const records = [];
  const singleFileGroups = new Map();
  const explicitFileGroups = new Map();

  for (const file of files) {
    const compilerCase = parseCompilerCase(file, casesRoot);
    if (compilerCase.hasExplicitFiles) {
      const shouldBatch = canBatchExplicitCase(compilerCase);
      const prepared = prepareCompilerCase(ts, compilerCase, repoRoot, shouldBatch);
      if (!shouldBatch) {
        collectProgramRecords(ts, prepared.options, prepared.virtualFiles, prepared.useCaseSensitive, records);
        continue;
      }

      const groupKey = stableOptionsKey(prepared.options, prepared.useCaseSensitive);
      let group = explicitFileGroups.get(groupKey);
      if (!group) {
        group = {
          options: prepared.options,
          useCaseSensitive: prepared.useCaseSensitive,
          virtualFiles: [],
        };
        explicitFileGroups.set(groupKey, group);
      }
      group.virtualFiles.push(...prepared.virtualFiles);
      continue;
    }

    const prepared = prepareCompilerCase(ts, compilerCase, repoRoot);
    const groupKey = stableOptionsKey(prepared.options, prepared.useCaseSensitive);
    let group = singleFileGroups.get(groupKey);
    if (!group) {
      group = {
        options: prepared.options,
        useCaseSensitive: prepared.useCaseSensitive,
        virtualFiles: [],
      };
      singleFileGroups.set(groupKey, group);
    }
    group.virtualFiles.push(...prepared.virtualFiles);
  }

  for (const group of singleFileGroups.values()) {
    collectProgramRecords(ts, group.options, group.virtualFiles, group.useCaseSensitive, records);
  }

  for (const group of explicitFileGroups.values()) {
    collectProgramRecords(ts, group.options, group.virtualFiles, group.useCaseSensitive, records);
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
