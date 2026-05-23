// This is some vibe-coded garbage, please pardon me, because I didn't feel like
// writing the conformance testing code myself yet.
use std::{
    any::Any,
    collections::{BTreeMap, BTreeSet},
    fmt,
    path::{Path, PathBuf},
    process::Command,
};

use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_span::{GetSpan, SourceType};

use super::*;

const TYPESCRIPT_CASES_ROOT: &str = "vendor/TypeScript/tests/cases";
const SNAPSHOT_PATH: &str = "tests/conformance/types_snapshot.txt";
const TSC_TYPES_PATH: &str = "target/conformance/tsc_types.tsv";
const OXC_TYPES_PATH: &str = "target/conformance/oxc_types.tsv";
const TSC_EXTRACTOR_PATH: &str = "tests/conformance/tsc_type_extractor.js";

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TypeRecord {
    path: String,
    start: u32,
    end: u32,
    text: String,
    ty: String,
}

impl TypeRecord {
    fn key(&self) -> TypeRecordKey {
        TypeRecordKey {
            start: self.start,
            end: self.end,
            text: self.text.clone(),
        }
    }

    fn to_tsv(&self) -> String {
        format!(
            "{}\t{}\t{}\t{}\t{}",
            self.path, self.start, self.end, self.text, self.ty
        )
    }

    fn from_tsv(line: &str) -> Result<Self, String> {
        let mut fields = line.splitn(5, '\t');
        let path = fields.next().ok_or("missing path")?.to_string();
        let start = fields
            .next()
            .ok_or("missing start")?
            .parse::<u32>()
            .map_err(|err| format!("invalid start: {err}"))?;
        let end = fields
            .next()
            .ok_or("missing end")?
            .parse::<u32>()
            .map_err(|err| format!("invalid end: {err}"))?;
        let text = fields.next().ok_or("missing text")?.to_string();
        let ty = fields.next().ok_or("missing type")?.to_string();

        Ok(Self {
            path,
            start,
            end,
            text,
            ty,
        })
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TypeRecordKey {
    start: u32,
    end: u32,
    text: String,
}

type TypeRecordMap = BTreeMap<TypeRecordKey, String>;

struct FileResult {
    path: String,
    matched_types: usize,
    errors: Vec<ComparisonError>,
}

impl FileResult {
    fn passed(&self) -> bool {
        self.errors.is_empty()
    }

    fn mismatched_types(&self) -> usize {
        self.errors.len()
    }

    fn total_types(&self) -> usize {
        self.matched_types + self.mismatched_types()
    }

    fn type_match_percentage(&self) -> f64 {
        percentage(self.matched_types, self.total_types())
    }
}

struct ComparisonStats {
    passed_files: usize,
    failed_files: usize,
    total_files: usize,
    matched_types: usize,
    mismatched_types: usize,
    total_types: usize,
}

impl ComparisonStats {
    fn from_results(results: &[FileResult]) -> Self {
        let total_files = results.len();
        let failed_files = results.iter().filter(|result| !result.passed()).count();
        let passed_files = total_files - failed_files;
        let matched_types = results.iter().map(|result| result.matched_types).sum();
        let mismatched_types = results.iter().map(FileResult::mismatched_types).sum();
        let total_types = matched_types + mismatched_types;

        Self {
            passed_files,
            failed_files,
            total_files,
            matched_types,
            mismatched_types,
            total_types,
        }
    }

    fn file_pass_percentage(&self) -> f64 {
        percentage(self.passed_files, self.total_files)
    }

    fn type_match_percentage(&self) -> f64 {
        percentage(self.matched_types, self.total_types)
    }

    fn summary(&self) -> String {
        format!(
            "files: {} passed, {} failed, {} total ({:.2}%)\ntypes: {} matched, {} mismatched, {} total ({:.2}%)",
            self.passed_files,
            self.failed_files,
            self.total_files,
            self.file_pass_percentage(),
            self.matched_types,
            self.mismatched_types,
            self.total_types,
            self.type_match_percentage()
        )
    }
}

struct ParsedFixture<'a> {
    checker: CheckerReturn<'a>,
}

struct ConformanceError(String);

type ConformanceResult = Result<(), ConformanceError>;

impl ConformanceError {
    fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl fmt::Debug for ConformanceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

enum ComparisonError {
    TypeMismatch {
        start: u32,
        end: u32,
        text: String,
        expected: String,
        actual: String,
    },
    MissingFromOxc {
        start: u32,
        end: u32,
        text: String,
        expected: String,
    },
    ExtraInOxc {
        start: u32,
        end: u32,
        text: String,
        actual: String,
    },
}

#[cfg(feature = "conformance-tsc")]
#[test]
fn typescript_compiler_type_extractor() -> ConformanceResult {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cases_root = repo_root.join(TYPESCRIPT_CASES_ROOT);
    let tsc_types_path = repo_root.join(TSC_TYPES_PATH);

    if !cases_root.exists() {
        return Err(ConformanceError::new(format!(
            "TypeScript test suite not found at {}. Run `git submodule update --init vendor/TypeScript`.",
            cases_root.display()
        )));
    }

    run_tsc_extractor(&repo_root, &cases_root, &tsc_types_path)?;
    eprintln!("TSC records: {}", tsc_types_path.display());
    Ok(())
}

#[cfg(feature = "conformance")]
#[test]
fn typescript_compiler_type_records() -> ConformanceResult {
    std::thread::Builder::new()
        .name("typescript_compiler_type_records".to_string())
        .stack_size(256 * 1024 * 1024)
        .spawn(run_typescript_compiler_type_records)
        .map_err(|err| {
            ConformanceError::new(format!("failed to spawn conformance test thread: {err}"))
        })?
        .join()
        .map_err(thread_panic_error)?
}

fn run_typescript_compiler_type_records() -> ConformanceResult {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cases_root = repo_root.join(TYPESCRIPT_CASES_ROOT);
    let tsc_types_path = repo_root.join(TSC_TYPES_PATH);
    let oxc_types_path = repo_root.join(OXC_TYPES_PATH);
    let snapshot_path = repo_root.join(SNAPSHOT_PATH);

    if !cases_root.exists() {
        return Err(ConformanceError::new(format!(
            "TypeScript test suite not found at {}. Run `git submodule update --init vendor/TypeScript`.",
            cases_root.display()
        )));
    }

    if !tsc_types_path.exists() {
        return Err(ConformanceError::new(format!(
            "TypeScript record cache not found at {}. Run `cargo conformance-tsc` first.",
            tsc_types_path.display()
        )));
    }

    let oxc_records = collect_oxc_records(&cases_root);
    write_records(&oxc_types_path, &oxc_records);

    let tsc_records = read_records(&tsc_types_path);
    let results = compare_records(&tsc_records, &oxc_records);
    let stats = ComparisonStats::from_results(&results);
    write_snapshot(&snapshot_path, &stats, &results);

    let summary = stats.summary();

    if stats.failed_files == 0 {
        eprintln!("TypeScript compiler case type-record conformance passed:\n{summary}");
        Ok(())
    } else {
        Err(ConformanceError::new(format!(
            "TypeScript compiler case type-record conformance failed:\n{summary}"
        )))
    }
}

fn thread_panic_error(payload: Box<dyn Any + Send>) -> ConformanceError {
    let message = payload
        .downcast_ref::<&str>()
        .map(|message| (*message).to_string())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "unknown panic payload".to_string());
    ConformanceError::new(format!("conformance test thread panicked: {message}"))
}

fn run_tsc_extractor(repo_root: &Path, cases_root: &Path, out_path: &Path) -> ConformanceResult {
    let extractor_path = repo_root.join(TSC_EXTRACTOR_PATH);
    let output = Command::new("node")
        .arg(&extractor_path)
        .arg("--repo-root")
        .arg(repo_root)
        .arg("--cases-root")
        .arg(cases_root)
        .arg("--out")
        .arg(out_path)
        .output()
        .map_err(|err| {
            ConformanceError::new(format!("failed to run {}: {err}", extractor_path.display()))
        })?;

    if !output.status.success() {
        return Err(ConformanceError::new(format!(
            "TypeScript type extractor failed with status {}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )));
    }

    Ok(())
}

fn discover_compiler_cases(cases_root: &Path) -> Vec<PathBuf> {
    let compiler_root = cases_root.join("compiler");
    let mut paths = std::fs::read_dir(&compiler_root)
        .unwrap_or_else(|err| {
            panic!(
                "failed to read TypeScript compiler cases directory {}: {err}",
                compiler_root.display()
            )
        })
        .map(|entry| {
            entry
                .unwrap_or_else(|err| {
                    panic!(
                        "failed to read TypeScript compiler cases directory entry in {}: {err}",
                        compiler_root.display()
                    )
                })
                .path()
        })
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "ts" || extension == "tsx")
        })
        .collect::<Vec<_>>();
    paths.sort();
    paths
}

fn collect_oxc_records(cases_root: &Path) -> Vec<TypeRecord> {
    let mut records = Vec::new();
    for path in discover_compiler_cases(cases_root) {
        let relative_path = relative_path(cases_root, &path);
        let source_text = match std::fs::read_to_string(&path) {
            Ok(source_text) => source_text,
            Err(_) => continue,
        };
        let allocator = Allocator::default();
        let parsed = match parse_fixture(&allocator, &source_text, &relative_path) {
            Ok(parsed) => parsed,
            Err(_) => continue,
        };
        records.extend(actual_symbol_records(&parsed.checker, &relative_path));
    }
    records.sort();
    records
}

fn parse_fixture<'a>(
    allocator: &'a Allocator,
    source_text: &'a str,
    fixture_path: &str,
) -> Result<ParsedFixture<'a>, String> {
    let source_type = SourceType::from_path(fixture_path).unwrap_or_else(|_| SourceType::ts());
    let parser = Parser::new(allocator, source_text, source_type);
    let ret = parser.parse();
    if !ret.errors.is_empty() {
        return Err(format!(
            "parse errors in TypeScript fixture {fixture_path}: {:?}",
            ret.errors
        ));
    }

    let program = allocator.alloc(ret.program);
    let semantic_ret = SemanticBuilder::new().build(program);
    if !semantic_ret.errors.is_empty() {
        return Err(format!(
            "semantic errors in TypeScript fixture {fixture_path}: {:?}",
            semantic_ret.errors
        ));
    }

    let checker = CheckerBuilder::new().build(program, semantic_ret.semantic);
    Ok(ParsedFixture { checker })
}

fn actual_symbol_records(checker: &CheckerReturn<'_>, path: &str) -> Vec<TypeRecord> {
    let scoping = checker.semantic().scoping();
    scoping
        .symbol_ids()
        .map(|symbol| {
            let span = scoping.symbol_span(symbol);
            TypeRecord {
                path: path.to_string(),
                start: span.start,
                end: span.end,
                text: sanitize(scoping.symbol_name(symbol)),
                ty: sanitize(
                    &checker.type_to_string(checker.get_type_of_symbol(symbol), NodeId::ROOT),
                ),
            }
        })
        .collect()
}

fn compare_records(tsc_records: &[TypeRecord], oxc_records: &[TypeRecord]) -> Vec<FileResult> {
    let tsc_by_file = records_by_file(tsc_records);
    let oxc_by_file = records_by_file(oxc_records);
    let mut files = BTreeSet::new();

    files.extend(tsc_by_file.keys().cloned());
    files.extend(oxc_by_file.keys().cloned());

    files
        .into_iter()
        .map(|path| {
            let mut errors = Vec::new();
            let mut matched_types = 0;
            let empty = TypeRecordMap::new();
            let tsc_by_key = tsc_by_file.get(&path).unwrap_or(&empty);
            let oxc_by_key = oxc_by_file.get(&path).unwrap_or(&empty);

            for (key, tsc_type) in tsc_by_key {
                match oxc_by_key.get(key) {
                    Some(oxc_type) if oxc_type == tsc_type => matched_types += 1,
                    Some(oxc_type) => errors.push(ComparisonError::TypeMismatch {
                        start: key.start,
                        end: key.end,
                        text: key.text.clone(),
                        expected: tsc_type.clone(),
                        actual: oxc_type.clone(),
                    }),
                    None => errors.push(ComparisonError::MissingFromOxc {
                        start: key.start,
                        end: key.end,
                        text: key.text.clone(),
                        expected: tsc_type.clone(),
                    }),
                }
            }

            for (key, oxc_type) in oxc_by_key {
                if !tsc_by_key.contains_key(key) {
                    errors.push(ComparisonError::ExtraInOxc {
                        start: key.start,
                        end: key.end,
                        text: key.text.clone(),
                        actual: oxc_type.clone(),
                    });
                }
            }

            FileResult {
                path,
                matched_types,
                errors,
            }
        })
        .collect()
}

fn records_by_file(records: &[TypeRecord]) -> BTreeMap<String, TypeRecordMap> {
    let mut by_file = BTreeMap::new();
    for record in records {
        by_file
            .entry(record.path.clone())
            .or_insert_with(TypeRecordMap::new)
            .insert(record.key(), record.ty.clone());
    }
    by_file
}

fn read_records(path: &Path) -> Vec<TypeRecord> {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("failed to read type records {}: {err}", path.display()));
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            TypeRecord::from_tsv(line).unwrap_or_else(|err| {
                panic!("invalid type record in {}: {err}: {line}", path.display())
            })
        })
        .collect()
}

fn write_records(path: &Path, records: &[TypeRecord]) {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).unwrap_or_else(|err| {
            panic!(
                "failed to create type record directory {}: {err}",
                parent.display()
            )
        });
    }

    let mut text = String::new();
    for record in records {
        text.push_str(&record.to_tsv());
        text.push('\n');
    }
    std::fs::write(path, text)
        .unwrap_or_else(|err| panic!("failed to write type records {}: {err}", path.display()));
}

fn relative_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

fn sanitize(value: &str) -> String {
    value.replace(['\t', '\r', '\n'], " ").trim().to_string()
}

fn percentage(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 {
        0.0
    } else {
        (numerator as f64 / denominator as f64) * 100.0
    }
}

fn write_snapshot(snapshot_path: &Path, stats: &ComparisonStats, results: &[FileResult]) {
    let mut snapshot = String::new();
    snapshot.push_str("# TypeScript compiler case type-record conformance snapshot\n");
    snapshot.push_str("# Generated by `cargo conformance`.\n");
    snapshot.push_str(&format!(
        "files: passed={} failed={} total={} pass_percentage={:.2}%\n",
        stats.passed_files,
        stats.failed_files,
        stats.total_files,
        stats.file_pass_percentage()
    ));
    snapshot.push_str(&format!(
        "types: matched={} mismatched={} total={} match_percentage={:.2}%\n\n",
        stats.matched_types,
        stats.mismatched_types,
        stats.total_types,
        stats.type_match_percentage()
    ));

    for result in results {
        let status = if result.passed() { "PASS" } else { "FAIL" };
        snapshot.push_str(&format!(
            "{status} {} matched_types={} mismatched_types={} total_types={} match_percentage={:.2}%\n",
            case_snapshot_path(&result.path),
            result.matched_types,
            result.mismatched_types(),
            result.total_types(),
            result.type_match_percentage()
        ));
        let mut line_starts = None;
        for error in &result.errors {
            write_snapshot_error(&mut snapshot, &result.path, &mut line_starts, error);
        }
    }

    if let Some(parent) = snapshot_path.parent() {
        std::fs::create_dir_all(parent).unwrap_or_else(|err| {
            panic!(
                "failed to create conformance snapshot directory {}: {err}",
                parent.display()
            )
        });
    }
    std::fs::write(snapshot_path, snapshot).unwrap_or_else(|err| {
        panic!(
            "failed to write conformance snapshot {}: {err}",
            snapshot_path.display()
        )
    });
}

fn case_snapshot_path(path: &str) -> String {
    format!("{TYPESCRIPT_CASES_ROOT}/{path}")
}

fn case_snapshot_location(path: &str, line_starts: &mut Option<Vec<u32>>, start: u32) -> String {
    let line = line_number_for_offset(path, line_starts, start);
    format!("{}:{}", case_snapshot_path(path), line)
}

fn line_number_for_offset(path: &str, line_starts: &mut Option<Vec<u32>>, offset: u32) -> usize {
    let line_starts = line_starts.get_or_insert_with(|| source_line_starts(path));
    match line_starts.binary_search(&offset) {
        Ok(index) => index + 1,
        Err(index) => index,
    }
}

fn source_line_starts(path: &str) -> Vec<u32> {
    let source_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(case_snapshot_path(path));
    let Ok(source_text) = std::fs::read_to_string(source_path) else {
        return vec![0];
    };

    let mut starts = vec![0];
    for (index, byte) in source_text.bytes().enumerate() {
        if byte == b'\n' {
            starts.push((index + 1) as u32);
        }
    }
    starts
}

fn write_snapshot_error(
    snapshot: &mut String,
    path: &str,
    line_starts: &mut Option<Vec<u32>>,
    error: &ComparisonError,
) {
    match error {
        ComparisonError::TypeMismatch {
            start,
            end: _,
            text,
            expected,
            actual,
        } => {
            snapshot.push_str(&format!(
                "  - {} `{}` type mismatch\n",
                case_snapshot_location(path, line_starts, *start),
                text
            ));
            snapshot.push_str(&format!("      expected: {expected}\n"));
            snapshot.push_str(&format!("      actual:   {actual}\n"));
        }
        ComparisonError::MissingFromOxc {
            start,
            end: _,
            text,
            expected,
        } => {
            snapshot.push_str(&format!(
                "  - {} `{}` missing from oxc output\n",
                case_snapshot_location(path, line_starts, *start),
                text
            ));
            snapshot.push_str(&format!("      expected: {expected}\n"));
            snapshot.push_str("      actual:   <missing>\n");
        }
        ComparisonError::ExtraInOxc {
            start,
            end: _,
            text,
            actual,
        } => {
            snapshot.push_str(&format!(
                "  - {} `{}` extra in oxc output\n",
                case_snapshot_location(path, line_starts, *start),
                text
            ));
            snapshot.push_str("      expected: <missing>\n");
            snapshot.push_str(&format!("      actual:   {actual}\n"));
        }
    }
}
