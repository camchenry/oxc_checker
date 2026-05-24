// This is some vibe-coded garbage, please pardon me, because I didn't feel like
// writing the conformance testing code myself yet.
use std::{
    any::Any,
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt,
    path::{Component, Path, PathBuf},
    process::Command,
};

use oxc_allocator::Allocator;
use oxc_ast::AstKind;
use oxc_span::GetSpan;

use super::*;

struct ConformanceSuite {
    name: &'static str,
    cases_root: &'static str,
    snapshot_path: &'static str,
    tsc_types_path: &'static str,
    oxc_types_path: &'static str,
    compiler_cases_only: bool,
    write_type_outputs: bool,
}

const TYPESCRIPT_SUITE: ConformanceSuite = ConformanceSuite {
    name: "TypeScript compiler case",
    cases_root: "vendor/TypeScript/tests/cases",
    snapshot_path: "tests/conformance/types_snapshot.txt",
    tsc_types_path: "target/conformance/tsc_types.tsv",
    oxc_types_path: "target/conformance/oxc_types.tsv",
    compiler_cases_only: true,
    write_type_outputs: false,
};

const CASES_SUITE: ConformanceSuite = ConformanceSuite {
    name: "local conformance case",
    cases_root: "tests/conformance/cases",
    snapshot_path: "tests/conformance/cases_snapshot.txt",
    tsc_types_path: "target/conformance/cases_tsc_types.tsv",
    oxc_types_path: "target/conformance/cases_oxc_types.tsv",
    compiler_cases_only: false,
    write_type_outputs: true,
};

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
}

struct FixtureProgramHost {
    files: HashMap<PathBuf, String>,
}

impl FixtureProgramHost {
    fn new(files: &[CompilerTestFile]) -> Self {
        let files = files
            .iter()
            .map(|file| {
                (
                    normalize_fixture_path(Path::new(&file.name)),
                    file.source_text.clone(),
                )
            })
            .collect();

        Self { files }
    }

    fn resolve_relative(
        &self,
        containing_file: &Path,
        specifier: &str,
    ) -> program::HostModuleResolution {
        if !(specifier.starts_with('.') || specifier.starts_with('/')) {
            return program::HostModuleResolution::External(specifier.to_string());
        }

        let containing_dir = containing_file.parent().unwrap_or_else(|| Path::new(""));
        let base = normalize_fixture_path(&containing_dir.join(specifier));
        if self.files.contains_key(&base) {
            return program::HostModuleResolution::Path(base);
        }

        for extension in ["ts", "tsx", "d.ts", "js", "jsx", "json"] {
            let mut candidate = base.clone();
            candidate.set_extension(extension);
            if self.files.contains_key(&candidate) {
                return program::HostModuleResolution::Path(candidate);
            }
        }

        for extension in ["ts", "tsx", "d.ts", "js", "jsx", "json"] {
            let candidate = base.join(format!("index.{extension}"));
            if self.files.contains_key(&candidate) {
                return program::HostModuleResolution::Path(candidate);
            }
        }

        program::HostModuleResolution::Missing(specifier.to_string())
    }
}

impl program::ProgramHost for FixtureProgramHost {
    fn read_source(&self, path: &Path) -> program::ProgramStoreResult<String> {
        let path = self.canonicalize_path(path);
        self.files
            .get(&path)
            .cloned()
            .ok_or_else(|| program::ProgramStoreError::ReadSource {
                path,
                message: "file not found".to_string(),
            })
    }

    fn canonicalize_path(&self, path: &Path) -> PathBuf {
        normalize_fixture_path(path)
    }

    fn resolve_module(
        &self,
        containing_file: &Path,
        specifier: &str,
    ) -> program::HostModuleResolution {
        self.resolve_relative(containing_file, specifier)
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

    fn into_message(self) -> String {
        self.0
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
    extract_tsc_type_records(&TYPESCRIPT_SUITE)
}

#[cfg(feature = "conformance-tsc")]
#[test]
fn custom_case_type_extractor() -> ConformanceResult {
    extract_tsc_type_records(&CASES_SUITE)
}

#[cfg(feature = "conformance")]
#[test]
fn typescript_compiler_type_records() -> ConformanceResult {
    run_type_record_conformance_on_thread("typescript_compiler_type_records", &TYPESCRIPT_SUITE)
}

#[cfg(feature = "conformance")]
#[test]
fn custom_case_type_records() -> ConformanceResult {
    run_type_record_conformance_on_thread("custom_case_type_records", &CASES_SUITE)
}

#[cfg(all(feature = "conformance", feature = "conformance-tsc"))]
#[test]
fn full_conformance() -> ConformanceResult {
    let mut failures = Vec::new();

    for suite in [&CASES_SUITE, &TYPESCRIPT_SUITE] {
        if let Err(err) = extract_tsc_type_records(suite) {
            failures.push(format!(
                "{} TypeScript record extraction failed:\n{}",
                suite.name,
                err.into_message()
            ));
            continue;
        }

        if let Err(err) = run_type_record_conformance_on_thread("full_conformance", suite) {
            failures.push(format!(
                "{} type-record comparison failed:\n{}",
                suite.name,
                err.into_message()
            ));
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(ConformanceError::new(format!(
            "conformance failed across {} suite(s):\n\n{}",
            failures.len(),
            failures.join("\n\n")
        )))
    }
}

fn run_type_record_conformance_on_thread(
    test_name: &'static str,
    suite: &'static ConformanceSuite,
) -> ConformanceResult {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(256 * 1024 * 1024)
        .spawn(move || run_type_record_conformance(suite))
        .map_err(|err| {
            ConformanceError::new(format!("failed to spawn conformance test thread: {err}"))
        })?
        .join()
        .map_err(thread_panic_error)?
}

fn extract_tsc_type_records(suite: &ConformanceSuite) -> ConformanceResult {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cases_root = repo_root.join(suite.cases_root);
    let tsc_types_path = repo_root.join(suite.tsc_types_path);

    ensure_cases_root(suite, &cases_root)?;
    run_tsc_extractor(&repo_root, suite, &cases_root, &tsc_types_path)?;
    Ok(())
}

fn run_type_record_conformance(suite: &ConformanceSuite) -> ConformanceResult {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cases_root = repo_root.join(suite.cases_root);
    let tsc_types_path = repo_root.join(suite.tsc_types_path);
    let oxc_types_path = repo_root.join(suite.oxc_types_path);
    let snapshot_path = repo_root.join(suite.snapshot_path);

    ensure_cases_root(suite, &cases_root)?;

    let oxc_records = collect_oxc_records(suite, &cases_root);
    write_records(&oxc_types_path, &oxc_records);
    write_type_outputs(suite, &cases_root, &oxc_records);

    let tsc_records = read_records(&tsc_types_path);
    let results = compare_records(&tsc_records, &oxc_records);
    let stats = ComparisonStats::from_results(&results);
    write_snapshot(&snapshot_path, suite, &stats, &results);

    let summary = stats.summary();

    if stats.failed_files == 0 {
        eprintln!("{} type-record conformance passed:\n{summary}", suite.name);
        Ok(())
    } else {
        Err(ConformanceError::new(format!(
            "{} type-record conformance failed:\n{summary}",
            suite.name
        )))
    }
}

fn ensure_cases_root(suite: &ConformanceSuite, cases_root: &Path) -> ConformanceResult {
    if cases_root.exists() {
        return Ok(());
    }

    Err(ConformanceError::new(format!(
        "{} root not found at {}",
        suite.name,
        cases_root.display()
    )))
}

fn thread_panic_error(payload: Box<dyn Any + Send>) -> ConformanceError {
    let message = payload
        .downcast_ref::<&str>()
        .map(|message| (*message).to_string())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "unknown panic payload".to_string());
    ConformanceError::new(format!("conformance test thread panicked: {message}"))
}

fn run_tsc_extractor(
    repo_root: &Path,
    suite: &ConformanceSuite,
    cases_root: &Path,
    out_path: &Path,
) -> ConformanceResult {
    let extractor_path = repo_root.join("tests/conformance/tsc_type_extractor.js");
    let case_discovery = if suite.compiler_cases_only {
        "compiler"
    } else {
        "all"
    };
    let output = Command::new("node")
        .arg(&extractor_path)
        .arg("--repo-root")
        .arg(repo_root)
        .arg("--cases-root")
        .arg(cases_root)
        .arg("--case-discovery")
        .arg(case_discovery)
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

fn discover_compiler_cases(suite: &ConformanceSuite, cases_root: &Path) -> Vec<PathBuf> {
    let search_root = if suite.compiler_cases_only {
        cases_root.join("compiler")
    } else {
        cases_root.to_path_buf()
    };
    let mut paths = Vec::new();
    discover_case_files(&search_root, &mut paths);
    paths.sort();
    paths
}

fn discover_case_files(root: &Path, paths: &mut Vec<PathBuf>) {
    for path in std::fs::read_dir(root)
        .unwrap_or_else(|err| {
            panic!(
                "failed to read conformance cases directory {}: {err}",
                root.display()
            )
        })
        .map(|entry| {
            entry
                .unwrap_or_else(|err| {
                    panic!(
                        "failed to read conformance cases directory entry in {}: {err}",
                        root.display()
                    )
                })
                .path()
        })
    {
        if path.is_dir() {
            discover_case_files(&path, paths);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "ts" || extension == "tsx")
        {
            paths.push(path);
        }
    }
}

fn collect_oxc_records(suite: &ConformanceSuite, cases_root: &Path) -> Vec<TypeRecord> {
    let mut records = Vec::new();
    for path in discover_compiler_cases(suite, cases_root) {
        let relative_path = relative_path(cases_root, &path);
        let source_text = match std::fs::read_to_string(&path) {
            Ok(source_text) => source_text,
            Err(_) => continue,
        };
        let compiler_case = parse_compiler_test_case(&source_text, &relative_path);
        let _settings = &compiler_case.settings;
        let allocator = Allocator::default();
        let parsed = match parse_fixture_program(&allocator, &compiler_case) {
            Ok(parsed) => parsed,
            Err(_) => continue,
        };
        for source_file in &compiler_case.files {
            let _file_settings = &source_file.settings;
            let Some(program_id) = parsed
                .store
                .id_for_path(&normalize_fixture_path(Path::new(&source_file.name)))
            else {
                continue;
            };
            records.extend(actual_identifier_records(
                &parsed.store,
                program_id,
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

fn normalize_fixture_path(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                normalized.pop();
            }
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(component.as_os_str()),
            Component::Normal(part) => normalized.push(part),
        }
    }
    normalized
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

fn parse_fixture_program<'a>(
    allocator: &'a Allocator,
    compiler_case: &CompilerTestCase,
) -> Result<ParsedFixture<'a>, String> {
    let host = FixtureProgramHost::new(&compiler_case.files);
    let mut builder = program::ProgramStoreBuilder::new(allocator, host);
    for source_file in &compiler_case.files {
        builder = builder.add_root_file(normalize_fixture_path(Path::new(&source_file.name)));
    }
    let store = builder.build().map_err(|err| err.to_string())?;

    Ok(ParsedFixture { store })
}

fn actual_identifier_records(
    store: &program::ProgramStore<'_>,
    program_id: program::ProgramId,
    path: &str,
) -> Vec<TypeRecord> {
    let checker = CheckerBuilder::new().build(store);
    store
        .entry(program_id)
        .unwrap()
        .semantic()
        .nodes()
        .iter_enumerated()
        .filter_map(|(node_id, node)| {
            actual_identifier_record(&checker, program_id, path, node_id, node.kind())
        })
        .collect()
}

fn actual_identifier_record(
    checker: &CheckerReturn<'_, '_>,
    program_id: program::ProgramId,
    path: &str,
    node_id: NodeId,
    kind: AstKind<'_>,
) -> Option<TypeRecord> {
    let node_ref = NodeRef::new(program_id, node_id);
    let (span, text, ty) = match kind {
        AstKind::BindingIdentifier(identifier) => {
            let symbol_id = identifier.symbol_id.get()?;
            let symbol = SymbolRef::new(program_id, symbol_id);
            (
                identifier.span,
                identifier.name.to_string(),
                checker.get_type_of_symbol(symbol),
            )
        }
        AstKind::IdentifierReference(identifier) => {
            checker.get_symbol_at_location(node_ref)?;
            (
                identifier.span,
                identifier.name.to_string(),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::IdentifierName(identifier) => {
            let ty = checker.get_type_at_location(node_ref);
            if ty == Ty::None {
                return None;
            }
            (identifier.span, identifier.name.to_string(), ty)
        }
        AstKind::TSPropertySignature(property) => {
            let span = property_key_span(&property.key)?;
            let text = property_key_name(&property.key)?;
            (span, text, checker.get_type_at_location(node_ref))
        }
        AstKind::ObjectProperty(property) => {
            let span = property_key_span(&property.key)?;
            let text = property_key_name(&property.key)?;
            (span, text, checker.get_type_at_location(node_ref))
        }
        AstKind::StaticMemberExpression(member) => (
            member.property.span,
            member.property.name.to_string(),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::MethodDefinition(method) => {
            let span = property_key_span(&method.key)?;
            let text = property_key_name(&method.key)?;
            (span, text, checker.get_type_at_location(node_ref))
        }
        AstKind::PropertyDefinition(property) => {
            let span = property_key_span(&property.key)?;
            let text = property_key_name(&property.key)?;
            (span, text, checker.get_type_at_location(node_ref))
        }
        AstKind::TSTypeAliasDeclaration(alias) => (
            alias.id.span,
            alias.id.name.to_string(),
            type_of_type_alias(alias),
        ),
        AstKind::TSTypeParameter(parameter) => (
            parameter.name.span,
            parameter.name.name.to_string(),
            Ty::Any,
        ),
        AstKind::TSTypeReference(reference) => {
            let (span, text) = ts_type_name_span_and_text(&reference.type_name)?;
            (span, text, Ty::Any)
        }
        _ => return None,
    };

    if ty == Ty::None {
        return None;
    }

    Some(TypeRecord {
        path: path.to_string(),
        start: span.start,
        end: span.end,
        text: sanitize(&text),
        ty: sanitize(&checker.type_to_string(ty, node_ref)),
    })
}

fn type_of_type_alias(alias: &oxc_ast::ast::TSTypeAliasDeclaration<'_>) -> Ty {
    if let Some(type_parameters) = &alias.type_parameters {
        return Ty::TypeReference {
            name: alias.id.name.to_string(),
            type_arguments: type_parameters
                .params
                .iter()
                .map(|parameter| Ty::TypeReference {
                    name: parameter.name.name.to_string(),
                    type_arguments: Vec::new(),
                })
                .collect(),
        };
    }

    let ty = Ty::from_ts_type(&alias.type_annotation);
    if ty == Ty::None { Ty::Any } else { ty }
}

fn ts_type_name_span_and_text(name: &TSTypeName<'_>) -> Option<(Span, String)> {
    match name {
        TSTypeName::IdentifierReference(identifier) => {
            Some((identifier.span, identifier.name.to_string()))
        }
        TSTypeName::QualifiedName(qualified) => {
            Some((qualified.span, ts_type_name_to_string(name)))
        }
        TSTypeName::ThisExpression(_) => None,
    }
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

fn write_type_outputs(suite: &ConformanceSuite, cases_root: &Path, records: &[TypeRecord]) {
    if !suite.write_type_outputs {
        return;
    }

    let mut records_by_path = BTreeMap::new();
    for record in records {
        records_by_path
            .entry(record.path.as_str())
            .or_insert_with(Vec::new)
            .push(record);
    }

    for path in discover_compiler_cases(suite, cases_root) {
        let relative_path = relative_path(cases_root, &path);
        let source_text = match std::fs::read_to_string(&path) {
            Ok(source_text) => source_text,
            Err(_) => continue,
        };
        let compiler_case = parse_compiler_test_case(&source_text, &relative_path);
        let mut output = String::new();

        for source_file in &compiler_case.files {
            let record_path = record_path(
                &relative_path,
                source_file,
                compiler_case.has_explicit_files,
            );
            let Some(source_records) = records_by_path.get(record_path.as_str()) else {
                continue;
            };
            write_type_output_for_source_file(
                &mut output,
                &source_file.source_text,
                source_records,
            );
        }

        let output_path = type_output_path(&path);
        std::fs::write(&output_path, output).unwrap_or_else(|err| {
            panic!(
                "failed to write type output {}: {err}",
                output_path.display()
            )
        });
    }
}

fn type_output_path(path: &Path) -> PathBuf {
    let file_name = path
        .file_name()
        .and_then(|file_name| file_name.to_str())
        .unwrap_or_else(|| panic!("invalid conformance case path {}", path.display()));
    path.with_file_name(format!("{file_name}.types"))
}

fn write_type_output_for_source_file(
    output: &mut String,
    source_text: &str,
    records: &[&TypeRecord],
) {
    let line_starts = line_starts_for_text(source_text);
    for record in records {
        if !output.is_empty() {
            output.push('\n');
        }

        let line_index = line_index_for_offset(&line_starts, record.start);
        let line_start = line_starts[line_index] as usize;
        let line_end = line_end_for_index(source_text, &line_starts, line_index);
        let span_start = (record.start as usize).clamp(line_start, line_end);
        let span_end = (record.end as usize).clamp(span_start, line_end);
        let start_column = display_column(source_text, line_start, span_start);
        let end_column = display_column(source_text, line_start, span_end);
        let marker_column = start_column.saturating_sub(1);
        let caret_count = (end_column.saturating_sub(start_column)).max(1);

        output.push_str(&source_text[line_start..line_end]);
        output.push('\n');
        output.push('>');
        output.extend(std::iter::repeat_n(' ', marker_column));
        output.extend(std::iter::repeat_n('^', caret_count));
        output.push_str("-: ");
        output.push_str(&record.ty);
        output.push('\n');
    }
}

fn line_index_for_offset(line_starts: &[u32], offset: u32) -> usize {
    match line_starts.binary_search(&offset) {
        Ok(index) => index,
        Err(0) => 0,
        Err(index) => index - 1,
    }
}

fn line_end_for_index(source_text: &str, line_starts: &[u32], line_index: usize) -> usize {
    line_starts
        .get(line_index + 1)
        .map_or(source_text.len(), |line_start| (*line_start as usize) - 1)
}

fn display_column(source_text: &str, line_start: usize, offset: usize) -> usize {
    source_text[line_start..offset].chars().count()
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

fn write_snapshot(
    snapshot_path: &Path,
    suite: &ConformanceSuite,
    stats: &ComparisonStats,
    results: &[FileResult],
) {
    let mut snapshot = String::new();
    snapshot.push_str(&format!(
        "# {} type-record conformance snapshot\n",
        suite.name
    ));
    snapshot.push_str("# Generated by `cargo conformance`.\n");
    snapshot.push_str(&format!("# Cases root: {}\n", suite.cases_root));
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
            case_snapshot_path(suite, &result.path),
            result.matched_types,
            result.mismatched_types(),
            result.total_types(),
            result.type_match_percentage()
        ));
        let mut line_starts = None;
        for error in &result.errors {
            write_snapshot_error(&mut snapshot, suite, &result.path, &mut line_starts, error);
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

fn case_snapshot_path(suite: &ConformanceSuite, path: &str) -> String {
    format!("{}/{path}", suite.cases_root)
}

fn case_snapshot_location(
    suite: &ConformanceSuite,
    path: &str,
    line_starts: &mut Option<Vec<u32>>,
    start: u32,
) -> String {
    let line = line_number_for_offset(suite, path, line_starts, start);
    format!("{}:{}", case_snapshot_path(suite, path), line)
}

fn line_number_for_offset(
    suite: &ConformanceSuite,
    path: &str,
    line_starts: &mut Option<Vec<u32>>,
    offset: u32,
) -> usize {
    let line_starts = line_starts.get_or_insert_with(|| source_line_starts(suite, path));
    match line_starts.binary_search(&offset) {
        Ok(index) => index + 1,
        Err(index) => index,
    }
}

fn source_line_starts(suite: &ConformanceSuite, path: &str) -> Vec<u32> {
    let (fixture_path, source_file_name) = path
        .split_once("::")
        .map_or((path, None), |(fixture_path, source_file_name)| {
            (fixture_path, Some(source_file_name))
        });
    let source_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(case_snapshot_path(suite, fixture_path));
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

    line_starts_for_text(source_text)
}

fn line_starts_for_text(source_text: &str) -> Vec<u32> {
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
    suite: &ConformanceSuite,
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
                case_snapshot_location(suite, path, line_starts, *start),
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
                case_snapshot_location(suite, path, line_starts, *start),
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
                case_snapshot_location(suite, path, line_starts, *start),
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

    #[test]
    fn type_output_renders_line_span_and_type() {
        let source_text = "let count: number = 1;\nlet label: string = \"ready\";";
        let record = TypeRecord {
            path: "compiler/basicPrimitives.ts".to_string(),
            start: 27,
            end: 32,
            text: "label".to_string(),
            ty: "string".to_string(),
        };
        let mut output = String::new();

        write_type_output_for_source_file(&mut output, source_text, &[&record]);

        assert_eq!(
            output,
            "let label: string = \"ready\";\n>   ^^^^^-: string\n"
        );
    }

    #[test]
    fn type_output_path_appends_types_extension() {
        assert_eq!(
            type_output_path(Path::new("tests/conformance/cases/compiler/example.ts")),
            PathBuf::from("tests/conformance/cases/compiler/example.ts.types")
        );
    }
}
