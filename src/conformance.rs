// This is some vibe-coded garbage, please pardon me, because I didn't feel like
// writing the conformance testing code myself yet.
use std::{
    any::Any,
    collections::{BTreeMap, BTreeSet, HashMap},
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
    store: program::ProgramStore<'a>,
    program_id: program::ProgramId,
}

struct FixtureProgramHost {
    path: PathBuf,
    source_text: String,
}

impl FixtureProgramHost {
    fn new(path: impl Into<PathBuf>, source_text: &str) -> Self {
        Self {
            path: path.into(),
            source_text: source_text.to_string(),
        }
    }
}

impl program::ProgramHost for FixtureProgramHost {
    fn read_source(&self, path: &Path) -> program::ProgramStoreResult<String> {
        if path == self.path {
            Ok(self.source_text.clone())
        } else {
            Err(program::ProgramStoreError::ReadSource {
                path: path.to_path_buf(),
                message: "file not found".to_string(),
            })
        }
    }

    fn canonicalize_path(&self, path: &Path) -> PathBuf {
        path.to_path_buf()
    }

    fn resolve_module(
        &self,
        _containing_file: &Path,
        specifier: &str,
    ) -> program::HostModuleResolution {
        program::HostModuleResolution::Missing(specifier.to_string())
    }
}

struct CompilerTestCase {
    settings: HashMap<String, String>,
    files: Vec<CompilerTestFile>,
    has_explicit_files: bool,
}

struct CompilerTestFile {
    name: String,
    source_text: String,
    settings: HashMap<String, String>,
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
        let compiler_case = parse_compiler_test_case(&source_text, &relative_path);
        let _settings = &compiler_case.settings;
        for source_file in &compiler_case.files {
            let _file_settings = &source_file.settings;
            let allocator = Allocator::default();
            let parsed =
                match parse_fixture(&allocator, &source_file.source_text, &source_file.name) {
                    Ok(parsed) => parsed,
                    Err(_) => continue,
                };
            records.extend(actual_symbol_records(
                &parsed.store,
                parsed.program_id,
                &record_path(
                    &relative_path,
                    source_file,
                    compiler_case.has_explicit_files,
                ),
            ));
        }
    }
    records.sort();
    records
}

fn parse_compiler_test_case(source_text: &str, fixture_path: &str) -> CompilerTestCase {
    let mut settings = HashMap::new();
    let mut files = Vec::new();
    let mut current_file_name = None;
    let mut current_file_settings = HashMap::new();
    let mut current_file_lines = Vec::new();
    let mut has_explicit_files = false;

    for line in source_text.lines() {
        if let Some((key, value)) = parse_compiler_directive(line) {
            if key == "filename" {
                has_explicit_files = true;
                if let Some(name) = current_file_name.replace(value) {
                    push_compiler_test_file(
                        &mut files,
                        name,
                        &mut current_file_lines,
                        std::mem::take(&mut current_file_settings),
                    );
                } else {
                    current_file_lines.clear();
                }
            } else if current_file_name.is_some() {
                current_file_settings.insert(key, value);
            } else {
                settings.insert(key, value);
            }
            continue;
        }

        current_file_lines.push(line.to_string());
    }

    let fallback_name = Path::new(fixture_path)
        .file_name()
        .and_then(|file_name| file_name.to_str())
        .unwrap_or(fixture_path)
        .to_string();
    push_compiler_test_file(
        &mut files,
        current_file_name.unwrap_or(fallback_name),
        &mut current_file_lines,
        current_file_settings,
    );

    CompilerTestCase {
        settings,
        files,
        has_explicit_files,
    }
}

fn parse_compiler_directive(line: &str) -> Option<(String, String)> {
    let comment = line.trim_start().strip_prefix("//")?.trim_start();
    let directive = comment.strip_prefix('@')?;
    let (key, value) = directive.split_once(':')?;
    let key = key.trim();
    if key.is_empty()
        || !key
            .chars()
            .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    {
        return None;
    }

    Some((key.to_ascii_lowercase(), value.trim().to_string()))
}

fn push_compiler_test_file(
    files: &mut Vec<CompilerTestFile>,
    name: String,
    lines: &mut Vec<String>,
    settings: HashMap<String, String>,
) {
    files.push(CompilerTestFile {
        name: normalize_test_file_name(&name),
        source_text: std::mem::take(lines).join("\n"),
        settings,
    });
}

fn normalize_test_file_name(name: &str) -> String {
    name.replace('\\', "/")
}

fn record_path(
    fixture_path: &str,
    source_file: &CompilerTestFile,
    has_explicit_files: bool,
) -> String {
    if has_explicit_files {
        format!("{fixture_path}::{}", source_file.name)
    } else {
        fixture_path.to_string()
    }
}

fn parse_fixture<'a>(
    allocator: &'a Allocator,
    source_text: &str,
    fixture_path: &str,
) -> Result<ParsedFixture<'a>, String> {
    let path = PathBuf::from(fixture_path);
    let host = FixtureProgramHost::new(path.clone(), source_text);
    let store = program::ProgramStoreBuilder::new(allocator, host)
        .add_root_file(path.clone())
        .build()
        .map_err(|err| err.to_string())?;
    let program_id = store.id_for_path(&path).ok_or_else(|| {
        format!("parsed fixture was not added to the program store: {fixture_path}")
    })?;

    Ok(ParsedFixture { store, program_id })
}

fn actual_symbol_records(
    store: &program::ProgramStore<'_>,
    program_id: program::ProgramId,
    path: &str,
) -> Vec<TypeRecord> {
    let checker = CheckerBuilder::new().build(store);
    let scoping = store.entry(program_id).unwrap().semantic().scoping();
    scoping
        .symbol_ids()
        .map(|symbol_id| {
            let span = scoping.symbol_span(symbol_id);
            let symbol = SymbolRef::new(program_id, symbol_id);
            TypeRecord {
                path: path.to_string(),
                start: span.start,
                end: span.end,
                text: sanitize(scoping.symbol_name(symbol_id)),
                ty: sanitize(&checker.type_to_string(
                    checker.get_type_of_symbol(symbol),
                    NodeRef::new(program_id, NodeId::ROOT),
                )),
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
    let (fixture_path, source_file_name) = path
        .split_once("::")
        .map_or((path, None), |(fixture_path, source_file_name)| {
            (fixture_path, Some(source_file_name))
        });
    let source_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(case_snapshot_path(fixture_path));
    let Ok(source_text) = std::fs::read_to_string(source_path) else {
        return vec![0];
    };
    let compiler_case = parse_compiler_test_case(&source_text, fixture_path);
    let Some(source_text) = compiler_case
        .files
        .iter()
        .find(|file| source_file_name.is_none_or(|name| file.name == name))
        .map(|file| file.source_text.as_str())
    else {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compiler_test_case_parser_collects_directives() {
        let parsed = parse_compiler_test_case(
            "// @target: es6\n// @module: commonjs\nlet value = false;",
            "compiler/example.ts",
        );

        assert_eq!(parsed.settings.get("target").unwrap(), "es6");
        assert_eq!(parsed.settings.get("module").unwrap(), "commonjs");
        assert!(!parsed.has_explicit_files);
        assert_eq!(parsed.files.len(), 1);
        assert_eq!(parsed.files[0].name, "example.ts");
        assert_eq!(parsed.files[0].source_text, "let value = false;");
    }

    #[test]
    fn compiler_test_case_parser_splits_filename_units() {
        let parsed = parse_compiler_test_case(
            "// @target: es2015\n// @filename: C:/foo/bar/Baz/src/utils.ts\nexport function exist() {}\n// @filename: C:/foo/bar/Baz/src/sample.ts\nimport { exit } from \"./utils.js\";\n\nexit()",
            "compiler/missingMemberErrorHasShortPath.ts",
        );

        assert_eq!(parsed.settings.get("target").unwrap(), "es2015");
        assert!(parsed.has_explicit_files);
        assert_eq!(parsed.files.len(), 2);
        assert_eq!(parsed.files[0].name, "C:/foo/bar/Baz/src/utils.ts");
        assert_eq!(parsed.files[0].source_text, "export function exist() {}");
        assert_eq!(parsed.files[1].name, "C:/foo/bar/Baz/src/sample.ts");
        assert_eq!(
            parsed.files[1].source_text,
            "import { exit } from \"./utils.js\";\n\nexit()"
        );
    }
}
