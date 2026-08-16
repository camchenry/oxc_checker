#!/usr/bin/env node
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import process from "node:process";
import { parseArgs as parseNodeArgs } from "node:util";
import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import {
  API,
  NodeBuilderFlags,
  SymbolFlags,
  type Checker,
  type Symbol as TypeScriptSymbol,
  type Type as TypeScriptType,
} from "typescript/unstable/sync";
import { createVirtualFileSystem } from "typescript/unstable/fs";
import {
  isExpressionStatement,
  isIdentifier,
  isPropertyAccessExpression,
  isTypeAliasDeclaration,
  type Node as TypeScriptNode,
  type SourceFile as TypeScriptSourceFile,
} from "typescript/unstable/ast";

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
  compilerOptions: Record<string, unknown>;
  configFileName: string;
  virtualFiles: VirtualFile[];
}

interface WorkerMessage {
  records?: string[];
  error?: string;
}

interface WorkerData {
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
const STRICT_COMPILER_OPTIONS: Record<string, boolean> = {
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
};

function conformanceTypeFormatFlags(): NodeBuilderFlags {
  return NodeBuilderFlags.NoTruncation
    | NodeBuilderFlags.UseStructuralFallback
    | NodeBuilderFlags.WriteTypeArgumentsOfSignature
    | NodeBuilderFlags.UseFullyQualifiedType
    | NodeBuilderFlags.WriteClassExpressionAsTypeLiteral
    | NodeBuilderFlags.UseAliasDefinedOutsideCurrentScope
    | NodeBuilderFlags.AllowUniqueESSymbolType
    | NodeBuilderFlags.NoTypeReduction;
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

function createCompilerOptions(compilerCase: CompilerCase): Record<string, unknown> {
  const options: Record<string, unknown> = {
    allowJs: true,
    checkJs: true,
    jsx: "preserve",
    module: "commonjs",
    noEmit: true,
    skipLibCheck: true,
    strict: true,
    target: "esnext",
    ...STRICT_COMPILER_OPTIONS,
  };

  for (const { key, value } of optionEntries(compilerCase.settings)) {
    const normalizedKey = key.toLowerCase();
    if (normalizedKey === "filename" || normalizedKey === "usecasesensitivefilenames") {
      continue;
    }
    options[key] = parseCompilerOptionValue(normalizedKey, value);
  }

  options.noEmit = true;
  options.skipLibCheck = true;
  return options;
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

function compilerCaseVirtualRoot(compilerCase: CompilerCase): string {
  return normalizeSlashes(path.join(
    path.dirname(compilerCase.physicalPath),
    ".oxc-conformance",
    path.basename(compilerCase.physicalPath),
  ));
}

function virtualFileName(
  compilerCase: CompilerCase,
  virtualRoot: string,
  sourceFile: CompilerFile,
): string {
  if (!compilerCase.hasExplicitFiles) {
    return normalizeSlashes(path.resolve(compilerCase.physicalPath));
  }
  const logicalPath = normalizeSlashes(sourceFile.name)
    .replace(/^[A-Za-z]:\//, "")
    .replace(/^\/+/, "");
  return normalizeSlashes(path.resolve(virtualRoot, logicalPath));
}

function isCompilableRootFile(fileName: string): boolean {
  return /\.(d\.ts|tsx?|jsx?|mjs|cjs|mts|cts)$/i.test(fileName);
}

function collectProgramRecords(
  api: API,
  task: CompilerTask,
  closeProject: string | undefined,
  records: string[],
): void {
  const snapshot = api.updateSnapshot({
    openProjects: [task.configFileName],
    closeProjects: closeProject ? [closeProject] : undefined,
  });
  try {
    const project = snapshot.getProject(task.configFileName);
    if (!project) {
      throw new Error(`nightly API did not open project ${task.configFileName}`);
    }
    for (const virtualFile of task.virtualFiles) {
      const sourceFile = project.program.getSourceFile(virtualFile.fileName);
      if (!sourceFile) {
        if (isCompilableRootFile(virtualFile.fileName)) {
          records.push(`${virtualFile.recordPath}\t0\t0\t<file>\t<missing source file>`);
        }
        continue;
      }
      try {
        records.push(...collectRecords(project.checker, sourceFile, virtualFile.recordPath));
      } catch (error) {
        const message = sanitize(error instanceof Error && error.message ? error.message : String(error));
        records.push(`${virtualFile.recordPath}\t0\t0\t<extractor-error>\t${message}`);
      }
    }
  } finally {
    snapshot.dispose();
  }
}

function createCompilerApi(tasks: CompilerTask[]): API {
  const files: Record<string, string> = {};
  for (const task of tasks) {
    for (const file of task.virtualFiles) {
      files[file.fileName] = file.content;
    }
    files[task.configFileName] = JSON.stringify({
      compilerOptions: task.compilerOptions,
      files: task.virtualFiles
        .filter((sourceFile) => isCompilableRootFile(sourceFile.fileName))
        .map((sourceFile) => sourceFile.fileName),
    });
  }
  return new API({
    cwd: process.cwd(),
    fs: createVirtualFileSystem(files),
  });
}

function prepareCompilerCase(compilerCase: CompilerCase): CompilerTask {
  const virtualRoot = compilerCaseVirtualRoot(compilerCase);
  const virtualFiles = compilerCase.files.map((sourceFile) => ({
    content: compilerCase.hasExplicitFiles ? virtualModuleContent(sourceFile.content) : sourceFile.content,
    fileName: virtualFileName(compilerCase, virtualRoot, sourceFile),
    recordPath: recordPathForFile(compilerCase, sourceFile),
  }));
  return {
    compilerOptions: createCompilerOptions(compilerCase),
    configFileName: normalizeSlashes(path.join(virtualRoot, "tsconfig.json")),
    virtualFiles,
  };
}

function virtualModuleContent(content: string): string {
  return `${content}${VIRTUAL_MODULE_MARKER}`;
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
  checker: Checker,
  sourceFile: TypeScriptSourceFile,
  relativePath: string,
  node: TypeScriptNode,
  byteOffsets: Uint32Array,
): string | undefined {
  if (isExpressionStatement(node)) {
    const typeText = typeToString(checker, checker.getTypeAtLocation(node.expression), node);
    const start = byteOffsets[node.getStart(sourceFile, false)];
    const end = byteOffsets[node.getEnd()];
    const text = sanitize(node.getText(sourceFile));
    return `${relativePath}\t${start}\t${end}\t${text}\t${sanitize(typeText)}`;
  }

  if (!isIdentifier(node)) {
    return undefined;
  }

  const symbol = checker.getSymbolAtLocation(node);
  const typeText = typeTextForIdentifier(checker, symbol, node);
  if (!typeText) {
    return undefined;
  }

  const start = byteOffsets[node.getStart(sourceFile, false)];
  const end = byteOffsets[node.getEnd()];
  const text = sanitize(node.getText(sourceFile));
  return `${relativePath}\t${start}\t${end}\t${text}\t${sanitize(typeText)}`;
}

function typeTextForIdentifier(
  checker: Checker,
  symbol: TypeScriptSymbol | undefined,
  node: TypeScriptNode,
): string | undefined {
  if (isTypeAliasDeclaration(node.parent) && node.parent.name === node) {
    return typeToString(
      checker,
      checker.getTypeFromTypeNode(node.parent.type),
      node,
      NodeBuilderFlags.InTypeAlias,
    );
  }
  if (symbol) {
    if (symbol.flags & SymbolFlags.Alias) {
      const aliased = checker.getAliasedSymbol(symbol);
      if (aliased && aliased !== symbol) {
        if (aliased.flags & SymbolFlags.TypeAlias) {
          return typeToString(
            checker,
            checker.getDeclaredTypeOfSymbol(aliased),
            node,
            NodeBuilderFlags.InTypeAlias,
          );
        }
        return typeToString(checker, checker.getTypeOfSymbolAtLocation(aliased, node), node);
      }
    }
    return typeToString(checker, checker.getTypeOfSymbolAtLocation(symbol, node), node);
  }
  if (isPropertyAccessExpression(node.parent) && node.parent.name === node) {
    return typeToString(checker, checker.getTypeAtLocation(node), node);
  }
  return undefined;
}

function typeToString(
  checker: Checker,
  type: TypeScriptType,
  node: TypeScriptNode,
  flags?: number,
): string {
  return checker.typeToString(type, node, (flags || 0) | conformanceTypeFormatFlags());
}

function collectRecords(
  checker: Checker,
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
    const record = recordForNode(checker, sourceFile, relativePath, node, byteOffsets);
    if (record) {
      records.push(record);
    }
    const children: TypeScriptNode[] = [];
    node.forEachChild((child: TypeScriptNode) => {
      children.push(child);
    });
    for (let index = children.length - 1; index >= 0; index -= 1) {
      stack.push(children[index]);
    }
  }
  return records;
}

function collectTaskRecords(api: API, task: CompilerTask, closeProject?: string): string[] {
  const records: string[] = [];
  collectProgramRecords(api, task, closeProject, records);
  return records;
}

function collectTaskBatchRecords(tasks: CompilerTask[]): string[] {
  const api = createCompilerApi(tasks);
  const records: string[] = [];
  let previousProject: string | undefined;
  try {
    for (const task of tasks) {
      records.push(...collectTaskRecords(api, task, previousProject));
      previousProject = task.configFileName;
    }
    return records;
  } finally {
    api.close();
  }
}

function buildCompilerTasks(casesRoot: string, files: string[]): CompilerTask[] {
  const tasks: CompilerTask[] = [];

  for (const file of files) {
    const compilerCase = parseCompilerCase(file, casesRoot);
    tasks.push(prepareCompilerCase(compilerCase));
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

function runWorker(tasks: CompilerTask[]): Promise<string[]> {
  return new Promise((resolve, reject) => {
    const worker = new Worker(new URL(import.meta.url), {
      workerData: { tasks },
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
  tasks: CompilerTask[],
  workerCount: number,
): Promise<string[]> {
  if (tasks.length === 0) {
    return [];
  }

  if (workerCount === 1 || tasks.length === 1) {
    return collectTaskBatchRecords(tasks);
  }

  const chunks = taskChunks(tasks, workerCount);
  const results = await Promise.all(chunks.map(runWorker));
  return results.flat();
}

async function workerMain(): Promise<void> {
  try {
    const data = workerData as WorkerData;
    const records = collectTaskBatchRecords(data.tasks);
    parentPort?.postMessage({ records });
  } catch (error) {
    parentPort?.postMessage({ error: error instanceof Error && error.stack ? error.stack : String(error) });
  }
}

async function main(): Promise<void> {
  const args = parseCliArgs(process.argv);
  const casesRoot = args.casesRoot;
  const outArg = args.out;
  const outPath = outArg === "-" ? undefined : path.resolve(outArg);
  const caseDiscovery = args.caseDiscovery;
  const workerCount = args.workerCount;
  const casePath = args.casePath;
  const files = casePath
    ? [resolveSingleCase(casesRoot, caseDiscovery, casePath)]
    : discoverCompilerCases(casesRoot, caseDiscovery);
  const tasks = buildCompilerTasks(casesRoot, files);
  const records = await collectRecordsFromTasks(tasks, workerCount);

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
