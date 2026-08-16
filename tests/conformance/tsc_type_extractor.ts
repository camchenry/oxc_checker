#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import process from "node:process";
import { pathToFileURL } from "node:url";
import { parseArgs as parseNodeArgs } from "node:util";
import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import type * as typescript from "typescript";

type TypeScript = typeof typescript & {
  optionDeclarations: readonly { name: string }[];
  getNormalizedAbsolutePath(fileName: string, currentDirectory: string): string;
  normalizePath(fileName: string): string;
};
type TypeChecker = typescript.TypeChecker;
type TypeScriptType = typescript.Type;
type TypeScriptSymbol = typescript.Symbol;
type TypeScriptNode = typescript.Node;
type TypeScriptSourceFile = typescript.SourceFile;
type TypeScriptCompilerOptions = typescript.CompilerOptions;

type CaseDiscovery = "compiler" | "all";

interface CompilerDirective {
  key: string;
  normalizedKey: string;
  value: string;
}

interface CompilerFile {
  name: string;
  content: string;
  options: Map<string, string>;
}

interface CompilerCase {
  physicalPath: string;
  relativePath: string;
  settings: Map<string, string>;
  files: CompilerFile[];
  hasExplicitFiles: boolean;
}

interface VirtualFile {
  content: string;
  fileName: string;
  recordPath: string;
}

interface CompilerTask {
  options: TypeScriptCompilerOptions;
  useCaseSensitive: boolean;
  virtualFiles: VirtualFile[];
}

interface WorkerMessage {
  records?: string[];
  error?: string;
}

interface WorkerData {
  repoRoot: string;
  tasks: CompilerTask[];
}

interface CliArgs {
  repoRoot: string;
  casesRoot: string;
  out: string;
  caseDiscovery: CaseDiscovery;
  workerCount: number;
  casePath?: string;
}

const DEFAULT_WORKERS = Math.max(
  1,
  Math.min(8, os.availableParallelism ? os.availableParallelism() : os.cpus().length || 1),
);
const VIRTUAL_MODULE_MARKER = "\nexport {};";
// oxc_checker always enables the full strict family, so case directives cannot disable it.
const STRICT_COMPILER_OPTIONS = {
  alwaysStrict: true,
  noImplicitAny: true,
  noImplicitThis: true,
  strict: true,
  strictBindCallApply: true,
  strictBuiltinIteratorReturn: true,
  strictFunctionTypes: true,
  strictNullChecks: true,
  strictPropertyInitialization: true,
  useUnknownInCatchVariables: true,
} satisfies TypeScriptCompilerOptions;

function conformanceTypeFormatFlags(ts: TypeScript): typescript.TypeFormatFlags {
  return ts.TypeFormatFlags.NoTruncation
    | ts.TypeFormatFlags.UseStructuralFallback
    | ts.TypeFormatFlags.WriteTypeArgumentsOfSignature
    | ts.TypeFormatFlags.UseFullyQualifiedType
    | ts.TypeFormatFlags.WriteClassExpressionAsTypeLiteral
    | ts.TypeFormatFlags.UseAliasDefinedOutsideCurrentScope
    | ts.TypeFormatFlags.AllowUniqueESSymbolType
    | ts.TypeFormatFlags.WriteArrowStyleSignature
    | ts.TypeFormatFlags.NoTypeReduction;
}

function parseCliArgs(argv: string[]): CliArgs {
  const { values } = parseNodeArgs({
    args: argv.slice(2),
    allowPositionals: false,
    options: {
      "case": { type: "string" },
      "case-discovery": { type: "string" },
      "cases-root": { type: "string" },
      "out": { type: "string" },
      "repo-root": { type: "string" },
      "workers": { type: "string" },
    },
    strict: true,
  });

  return {
    repoRoot: path.resolve(values["repo-root"] || process.cwd()),
    casesRoot: path.resolve(requiredArg(values["cases-root"], "cases-root")),
    out: requiredArg(values.out, "out"),
    caseDiscovery: parseCaseDiscovery(values["case-discovery"]),
    workerCount: parseWorkerCount(values.workers),
    casePath: values.case,
  };
}

function requiredArg(value: string | undefined, name: string): string {
  if (value === undefined) {
    throw new Error(`missing required --${name} argument`);
  }
  return value;
}

function parseCaseDiscovery(value: string | undefined): CaseDiscovery {
  if (value === undefined || value === "compiler" || value === "all") {
    return value || "compiler";
  }
  throw new Error("--case-discovery must be either compiler or all");
}

function parseWorkerCount(value: string | undefined): number {
  if (value === undefined) {
    return DEFAULT_WORKERS;
  }

  const count = Number(value);
  if (!Number.isInteger(count) || count < 1) {
    throw new Error("--workers must be a positive integer");
  }
  return count;
}

async function loadTypeScript(repoRoot: string): Promise<TypeScript> {
  const candidates: string[] = [];
  if (process.env.TYPESCRIPT_MODULE) {
    candidates.push(process.env.TYPESCRIPT_MODULE);
  }
  candidates.push(path.join(repoRoot, "target", "conformance", "node_modules", "typescript", "lib", "typescript.js"));
  candidates.push(path.join(repoRoot, "vendor", "TypeScript", "built", "local", "typescript.js"));
  candidates.push(path.join(repoRoot, "vendor", "TypeScript", "lib", "typescript.js"));

  for (const candidate of candidates) {
    if (candidate && fs.existsSync(candidate)) {
      return loadTypeScriptModule(pathToFileURL(candidate).href);
    }
  }

  try {
    return await loadTypeScriptModule("typescript");
  } catch {
    const message = [
      "Unable to load the TypeScript compiler API.",
      "Install the npm `typescript` package, build the TypeScript submodule, or set TYPESCRIPT_MODULE=/path/to/typescript.js.",
      "Tried:",
      ...candidates.map((candidate) => `  - ${candidate}`),
      `  - import("typescript") from ${process.cwd()}`,
    ].join("\n");
    throw new Error(message);
  }
}

async function loadTypeScriptModule(specifier: string): Promise<TypeScript> {
  const module = await import(specifier);
  return module.default ?? module;
}

function discoverCompilerCases(casesRoot: string, caseDiscovery: CaseDiscovery): string[] {
  const searchRoot = caseDiscovery === "compiler"
    ? path.join(casesRoot, "compiler")
    : casesRoot;
  const files: string[] = [];
  discoverCaseFiles(searchRoot, files);
  return files.sort();
}

function resolveSingleCase(casesRoot: string, caseDiscovery: CaseDiscovery, casePath: string): string {
  const file = path.resolve(casePath);
  const relative = normalizeSlashes(path.relative(casesRoot, file));
  if (relative.startsWith("../") || relative === ".." || path.isAbsolute(relative)) {
    throw new Error(`--case must be inside --cases-root: ${casePath}`);
  }
  if (caseDiscovery === "compiler" && relative !== "compiler" && !relative.startsWith("compiler/")) {
    throw new Error(`--case must be inside the compiler cases directory: ${casePath}`);
  }
  if (!/\.tsx?$/.test(file) || !fs.statSync(file, { throwIfNoEntry: false })?.isFile()) {
    throw new Error(`--case must be an existing .ts or .tsx file: ${casePath}`);
  }
  return file;
}

function discoverCaseFiles(root: string, files: string[]): void {
  for (const entry of fs.readdirSync(root, { withFileTypes: true })) {
    const file = path.join(root, entry.name);
    if (entry.isDirectory()) {
      discoverCaseFiles(file, files);
    } else if (entry.isFile() && (/\.tsx?$/.test(entry.name))) {
      files.push(file);
    }
  }
}

function parseCompilerDirective(line: string): CompilerDirective | undefined {
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

function parseCompilerCase(file: string, casesRoot: string): CompilerCase {
  const sourceText = fs.readFileSync(file, "utf8");
  const relativePath = path.relative(casesRoot, file).replace(/\\/g, "/");
  const settings = new Map<string, string>();
  const files: CompilerFile[] = [];
  let currentFileName: string | undefined;
  let currentFileOptions = new Map<string, string>();
  let currentFileLines: string[] = [];
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

function pushCompilerFile(
  files: CompilerFile[],
  name: string,
  lines: string[],
  options: Map<string, string>,
): void {
  files.push({
    name: normalizeSlashes(name),
    content: lines.join("\n"),
    options,
  });
}

function normalizeSlashes(value: string): string {
  return String(value).replace(/\\/g, "/");
}

function recordPathForFile(compilerCase: CompilerCase, sourceFile: CompilerFile): string {
  return compilerCase.hasExplicitFiles
    ? `${compilerCase.relativePath}::${sourceFile.name}`
    : compilerCase.relativePath;
}

function optionEntries(settings: Map<string, string>): Array<{ key: string; value: string }> {
  return Array.from(settings, ([key, value]) => ({ key, value }));
}

function compilerOptionNameMap(ts: TypeScript): Map<string, string> {
  return new Map(ts.optionDeclarations.map((option) => [option.name.toLowerCase(), option.name]));
}

function compilerSettingsKey(settings: Map<string, string>): string {
  return JSON.stringify(Array.from(settings).sort(([left], [right]) => left.localeCompare(right)));
}

function createCompilerOptions(
  ts: TypeScript,
  compilerCase: CompilerCase,
  repoRoot: string,
  optionNameMap: Map<string, string>,
): TypeScriptCompilerOptions {
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
  const jsonOptions: Record<string, unknown> = {};

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
  return {
    ...baseOptions,
    ...converted.options,
    ...STRICT_COMPILER_OPTIONS,
    noEmit: true,
    skipLibCheck: true,
  };
}

function createCompilerOptionsCache(
  ts: TypeScript,
  repoRoot: string,
): (compilerCase: CompilerCase) => TypeScriptCompilerOptions {
  const optionNameMap = compilerOptionNameMap(ts);
  const cache = new Map<string, TypeScriptCompilerOptions>();
  return (compilerCase) => {
    const key = compilerSettingsKey(compilerCase.settings);
    let options = cache.get(key);
    if (!options) {
      options = createCompilerOptions(ts, compilerCase, repoRoot, optionNameMap);
      cache.set(key, options);
    }
    return options;
  };
}

function parseCompilerOptionValue(key: string, value: string): boolean | string | string[] {
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

function useCaseSensitiveFileNames(ts: TypeScript, compilerCase: CompilerCase): boolean {
  const setting = Array.from(compilerCase.settings).find(([key]) => key.toLowerCase() === "usecasesensitivefilenames");
  if (!setting) {
    return ts.sys.useCaseSensitiveFileNames;
  }
  return /^true$/i.test(setting[1].trim());
}

function virtualFileName(ts: TypeScript, compilerCase: CompilerCase, sourceFile: CompilerFile): string {
  if (!compilerCase.hasExplicitFiles) {
    return normalizeSlashes(path.resolve(compilerCase.physicalPath));
  }
  const caseDirectory = normalizeSlashes(path.dirname(compilerCase.physicalPath));
  return normalizeSlashes(ts.getNormalizedAbsolutePath(sourceFile.name, caseDirectory));
}

function canonicalFileName(ts: TypeScript, fileName: string, useCaseSensitive: boolean): string {
  const normalized = normalizeSlashes(ts.normalizePath(fileName));
  return useCaseSensitive ? normalized : normalized.toLowerCase();
}

function createVirtualCompilerHost(
  ts: TypeScript,
  options: TypeScriptCompilerOptions,
  virtualFiles: VirtualFile[],
  useCaseSensitive: boolean,
) {
  const defaultHost = ts.createCompilerHost(options, true);
  const filesByName = new Map<string, VirtualFile>();
  const directories = new Set<string>();
  for (const file of virtualFiles) {
    filesByName.set(canonicalFileName(ts, file.fileName, useCaseSensitive), file);
    addAncestorDirectories(ts, directories, file.fileName, useCaseSensitive);
  }

  return {
    ...defaultHost,
    useCaseSensitiveFileNames: () => useCaseSensitive,
    getCanonicalFileName: (fileName: string) => canonicalFileName(ts, fileName, useCaseSensitive),
    getCurrentDirectory: () => normalizeSlashes(process.cwd()),
    trace: () => {},
    fileExists: (fileName: string) => filesByName.has(canonicalFileName(ts, fileName, useCaseSensitive)) || defaultHost.fileExists(fileName),
    directoryExists: (dirName: string) => directories.has(canonicalFileName(ts, dirName, useCaseSensitive))
      || (defaultHost.directoryExists ? defaultHost.directoryExists(dirName) : true),
    readFile: (fileName: string) => {
      const file = filesByName.get(canonicalFileName(ts, fileName, useCaseSensitive));
      return file ? file.content : defaultHost.readFile(fileName);
    },
    getSourceFile: (
      fileName: string,
      languageVersion: typescript.ScriptTarget | typescript.CreateSourceFileOptions,
      onError?: (message: string) => void,
      shouldCreateNewSourceFile?: boolean,
    ) => {
      const file = filesByName.get(canonicalFileName(ts, fileName, useCaseSensitive));
      if (file) {
        return ts.createSourceFile(file.fileName, file.content, languageVersion, true);
      }
      return defaultHost.getSourceFile(fileName, languageVersion, onError, shouldCreateNewSourceFile);
    },
  };
}

function addAncestorDirectories(
  ts: TypeScript,
  directories: Set<string>,
  fileName: string,
  useCaseSensitive: boolean,
): void {
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

function isCompilableRootFile(fileName: string): boolean {
  return /\.(d\.ts|tsx?|jsx?|mjs|cjs|mts|cts)$/i.test(fileName);
}

function collectProgramRecords(
  ts: TypeScript,
  options: TypeScriptCompilerOptions,
  virtualFiles: VirtualFile[],
  useCaseSensitive: boolean,
  records: string[],
): void {
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
      const message = sanitize(error instanceof Error && error.message ? error.message : String(error));
      records.push(`${virtualFile.recordPath}\t0\t0\t<extractor-error>\t${message}`);
    }
  }

  for (const sourceFile of virtualFiles) {
    if (isCompilableRootFile(sourceFile.fileName) && !program.getSourceFile(sourceFile.fileName)) {
      records.push(`${sourceFile.recordPath}\t0\t0\t<file>\t<missing source file>`);
    }
  }
}

function prepareCompilerCase(
  ts: TypeScript,
  compilerCase: CompilerCase,
  compilerOptionsForCase: (compilerCase: CompilerCase) => TypeScriptCompilerOptions,
) {
  const options = compilerOptionsForCase(compilerCase);
  const useCaseSensitive = useCaseSensitiveFileNames(ts, compilerCase);
  const virtualFiles = compilerCase.files.map((sourceFile) => ({
    content: compilerCase.hasExplicitFiles ? virtualModuleContent(sourceFile.content) : sourceFile.content,
    fileName: virtualFileName(ts, compilerCase, sourceFile),
    recordPath: recordPathForFile(compilerCase, sourceFile),
  }));
  return { compilerCase, options, useCaseSensitive, virtualFiles };
}

function virtualModuleContent(content: string): string {
  return `${content}${VIRTUAL_MODULE_MARKER}`;
}

function compilerTaskFromPrepared(prepared: { options: TypeScriptCompilerOptions; useCaseSensitive: boolean; virtualFiles: VirtualFile[] }): CompilerTask {
  return {
    options: prepared.options,
    useCaseSensitive: prepared.useCaseSensitive,
    virtualFiles: prepared.virtualFiles,
  };
}

function taskWeight(task: CompilerTask): number {
  return task.virtualFiles.length;
}

function sanitize(value: unknown): string {
  return String(value).replace(/[\t\r\n]+/g, " ").trim();
}

function utf16ToUtf8ByteOffsets(sourceText: string): Uint32Array {
  const offsets = new Uint32Array(sourceText.length + 1);
  let utf8Offset = 0;

  for (let utf16Offset = 0; utf16Offset < sourceText.length;) {
    offsets[utf16Offset] = utf8Offset;
    const codePoint = sourceText.codePointAt(utf16Offset) ?? 0;
    const utf16Width = codePoint > 0xffff ? 2 : 1;
    const utf8Width = codePoint <= 0x7f ? 1 : codePoint <= 0x7ff ? 2 : codePoint <= 0xffff ? 3 : 4;

    if (utf16Width === 2) {
      offsets[utf16Offset + 1] = utf8Offset;
    }

    utf16Offset += utf16Width;
    utf8Offset += utf8Width;
  }

  offsets[sourceText.length] = utf8Offset;
  return offsets;
}

function recordForNode(
  ts: TypeScript,
  checker: TypeChecker,
  sourceFile: TypeScriptSourceFile,
  relativePath: string,
  node: TypeScriptNode,
  byteOffsets: Uint32Array,
): string | undefined {
  if (ts.isExpressionStatement(node)) {
    const typeText = typeToString(ts, checker, checker.getTypeAtLocation(node.expression), node);
    const start = byteOffsets[node.getStart(sourceFile, false)];
    const end = byteOffsets[node.getEnd()];
    const text = sanitize(node.getText(sourceFile));
    return `${relativePath}\t${start}\t${end}\t${text}\t${sanitize(typeText)}`;
  }

  if (!ts.isIdentifier(node)) {
    return undefined;
  }

  const symbol = checker.getSymbolAtLocation(node);
  const typeText = typeTextForIdentifier(ts, checker, symbol, node);
  if (!typeText) {
    return undefined;
  }

  const start = byteOffsets[node.getStart(sourceFile, false)];
  const end = byteOffsets[node.getEnd()];
  const text = sanitize(node.getText(sourceFile));
  return `${relativePath}\t${start}\t${end}\t${text}\t${sanitize(typeText)}`;
}

function typeTextForIdentifier(
  ts: TypeScript,
  checker: TypeChecker,
  symbol: TypeScriptSymbol | undefined,
  node: TypeScriptNode,
): string | undefined {
  if (ts.isTypeAliasDeclaration(node.parent) && node.parent.name === node) {
    return typeToString(
      ts,
      checker,
      checker.getTypeFromTypeNode(node.parent.type),
      node,
      ts.TypeFormatFlags.InTypeAlias,
    );
  }
  if (symbol) {
    if (symbol.flags & ts.SymbolFlags.Alias) {
      const aliased = checker.getAliasedSymbol(symbol);
      if (aliased && aliased !== symbol) {
        if (aliased.declarations?.some((declaration: TypeScriptNode) => ts.isTypeAliasDeclaration(declaration))) {
          return typeToString(
            ts,
            checker,
            checker.getDeclaredTypeOfSymbol(aliased),
            node,
            ts.TypeFormatFlags.InTypeAlias,
          );
        }
        return typeToString(ts, checker, checker.getTypeOfSymbolAtLocation(aliased, node), node);
      }
    }
    return typeToString(ts, checker, checker.getTypeOfSymbolAtLocation(symbol, node), node);
  }
  if (ts.isPropertyAccessExpression(node.parent) && node.parent.name === node) {
    return typeToString(ts, checker, checker.getTypeAtLocation(node), node);
  }
  return undefined;
}

function typeToString(
  ts: TypeScript,
  checker: TypeChecker,
  type: TypeScriptType,
  node: TypeScriptNode,
  flags?: number,
): string {
  return checker.typeToString(type, node, (flags || 0) | conformanceTypeFormatFlags(ts));
}

function collectRecords(
  ts: TypeScript,
  checker: TypeChecker,
  sourceFile: TypeScriptSourceFile,
  relativePath: string,
): string[] {
  const records: string[] = [];
  const byteOffsets = utf16ToUtf8ByteOffsets(sourceFile.text);
  const stack: TypeScriptNode[] = [sourceFile];
  while (stack.length > 0) {
    const node = stack.pop();
    if (!node) {
      continue;
    }
    const record = recordForNode(ts, checker, sourceFile, relativePath, node, byteOffsets);
    if (record) {
      records.push(record);
    }
    const children: TypeScriptNode[] = [];
    ts.forEachChild(node, (child: TypeScriptNode) => {
      children.push(child);
    });
    for (let index = children.length - 1; index >= 0; index -= 1) {
      stack.push(children[index]);
    }
  }
  return records;
}

function collectTaskRecords(ts: TypeScript, task: CompilerTask): string[] {
  const records: string[] = [];
  collectProgramRecords(ts, task.options, task.virtualFiles, task.useCaseSensitive, records);
  return records;
}

function buildCompilerTasks(ts: TypeScript, repoRoot: string, casesRoot: string, files: string[]): CompilerTask[] {
  const tasks: CompilerTask[] = [];
  const compilerOptionsForCase = createCompilerOptionsCache(ts, repoRoot);

  for (const file of files) {
    const compilerCase = parseCompilerCase(file, casesRoot);
    const prepared = prepareCompilerCase(ts, compilerCase, compilerOptionsForCase);
    tasks.push(compilerTaskFromPrepared(prepared));
  }

  return tasks;
}

function taskChunks(tasks: CompilerTask[], workerCount: number): CompilerTask[][] {
  const chunkCount = Math.min(workerCount, tasks.length);
  const chunks = Array.from({ length: chunkCount }, () => ({ weight: 0, tasks: [] as CompilerTask[] }));
  const sortedTasks = [...tasks].sort((left, right) => taskWeight(right) - taskWeight(left));

  for (const task of sortedTasks) {
    let target = chunks[0];
    for (const chunk of chunks) {
      if (chunk.weight < target.weight) {
        target = chunk;
      }
    }
    target.tasks.push(task);
    target.weight += taskWeight(task);
  }

  return chunks.map((chunk) => chunk.tasks).filter((chunk) => chunk.length > 0);
}

function runWorker(repoRoot: string, tasks: CompilerTask[]): Promise<string[]> {
  return new Promise((resolve, reject) => {
    const worker = new Worker(new URL(import.meta.url), {
      workerData: { repoRoot, tasks },
    });
    let settled = false;

    worker.on("message", (message: WorkerMessage) => {
      settled = true;
      if (message.error) {
        reject(new Error(message.error));
      } else {
        resolve(message.records ?? []);
      }
    });
    worker.on("error", (error: Error) => {
      settled = true;
      reject(error);
    });
    worker.on("exit", (code: number) => {
      if (!settled && code !== 0) {
        reject(new Error(`worker stopped with exit code ${code}`));
      }
    });
  });
}

async function collectRecordsFromTasks(
  ts: TypeScript,
  repoRoot: string,
  tasks: CompilerTask[],
  workerCount: number,
): Promise<string[]> {
  if (tasks.length === 0) {
    return [];
  }

  if (workerCount === 1 || tasks.length === 1) {
    return tasks.flatMap((task) => collectTaskRecords(ts, task));
  }

  const chunks = taskChunks(tasks, workerCount);
  const results = await Promise.all(chunks.map((chunk) => runWorker(repoRoot, chunk)));
  return results.flat();
}

async function workerMain(): Promise<void> {
  try {
    const data = workerData as WorkerData;
    const ts = await loadTypeScript(data.repoRoot);
    const records = data.tasks.flatMap((task) => collectTaskRecords(ts, task));
    parentPort?.postMessage({ records });
  } catch (error) {
    parentPort?.postMessage({ error: error instanceof Error && error.stack ? error.stack : String(error) });
  }
}

async function main(): Promise<void> {
  const args = parseCliArgs(process.argv);
  const repoRoot = args.repoRoot;
  const casesRoot = args.casesRoot;
  const outArg = args.out;
  const outPath = outArg === "-" ? undefined : path.resolve(outArg);
  const caseDiscovery = args.caseDiscovery;
  const workerCount = args.workerCount;
  const ts = await loadTypeScript(repoRoot);
  const casePath = args.casePath;
  const files = casePath
    ? [resolveSingleCase(casesRoot, caseDiscovery, casePath)]
    : discoverCompilerCases(casesRoot, caseDiscovery);
  const tasks = buildCompilerTasks(ts, repoRoot, casesRoot, files);
  const records = await collectRecordsFromTasks(ts, repoRoot, tasks, workerCount);

  records.sort();
  if (outArg === "-") {
    process.stdout.write(`${records.join("\n")}\n`);
    return;
  }
  if (!outPath) {
    throw new Error("missing output path");
  }
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, `${records.join("\n")}\n`);
}

if (isMainThread) {
  main().catch((error) => {
    console.error(error && error.stack ? error.stack : String(error));
    process.exit(1);
  });
} else {
  workerMain().catch((error) => {
    parentPort?.postMessage({ error: error instanceof Error && error.stack ? error.stack : String(error) });
  });
}
