// This is some vibe-coded garbage, please pardon me, because I didn't feel like
// writing the conformance testing code myself yet.
use std::{
    any::Any,
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt, io,
    path::{Component, Path, PathBuf},
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, AtomicUsize, Ordering},
        mpsc,
    },
    time::{Duration, Instant},
};

use oxc_allocator::Allocator;
use oxc_ast::{
    AstKind, AstType,
    ast::{MethodDefinitionKind, PropertyKey, Statement},
};
use oxc_resolver::{FileMetadata, FileSystem, ResolveError, ResolveOptions, ResolverGeneric};
use oxc_semantic::NodeId;
use oxc_span::{GetSpan, Span};
use oxc_syntax::module_record::{ExportEntry, ExportLocalName};
use rayon::prelude::*;
use terminal_size::{Width, terminal_size};

use crate::checker::{Checker, CheckerBuilder, CheckerReturn, NodeRef};

use super::*;

struct ConformanceSuite {
    name: &'static str,
    cases_root: &'static str,
    snapshot_path: &'static str,
    tsc_types_path: &'static str,
    compiler_cases_only: bool,
    write_type_outputs: bool,
    type_outputs_root: Option<&'static str>,
}

const CONFORMANCE_THREAD_STACK_SIZE: usize = 256 * 1024 * 1024;
const MIN_FILES_PER_PREPARED_BATCH: usize = 4;
const VIRTUAL_MODULE_MARKER: &str = "\nexport {};";

const TYPESCRIPT_SUITE: ConformanceSuite = ConformanceSuite {
    name: "TypeScript compiler case",
    cases_root: "vendor/TypeScript/tests/cases",
    snapshot_path: "tests/conformance/types_snapshot.txt",
    tsc_types_path: "tests/conformance/tsc-types/typescript_tsc_types.tsv",
    compiler_cases_only: true,
    write_type_outputs: false,
    type_outputs_root: None,
};

const CASES_SUITE: ConformanceSuite = ConformanceSuite {
    name: "local conformance case",
    cases_root: "tests/conformance/cases",
    snapshot_path: "tests/conformance/cases_snapshot.txt",
    tsc_types_path: "tests/conformance/tsc-types/cases_tsc_types.tsv",
    compiler_cases_only: false,
    write_type_outputs: true,
    type_outputs_root: None,
};

const EXTERNAL_LIBRARY_SUITE: ConformanceSuite = ConformanceSuite {
    name: "external library fixture",
    cases_root: "tests/conformance/external",
    snapshot_path: "tests/conformance/external_snapshot.txt",
    tsc_types_path: "tests/conformance/tsc-types/external_tsc_types.tsv",
    compiler_cases_only: false,
    write_type_outputs: true,
    type_outputs_root: None,
};

const STANDARD_LIBRARY_SUITE: ConformanceSuite = ConformanceSuite {
    name: "standard library declaration",
    cases_root: "src/lib",
    snapshot_path: "tests/conformance/lib_snapshot.txt",
    tsc_types_path: "tests/conformance/tsc-types/lib_tsc_types.tsv",
    compiler_cases_only: false,
    write_type_outputs: true,
    type_outputs_root: Some("tests/conformance/lib"),
};

fn all_conformance_suites() -> [&'static ConformanceSuite; 4] {
    [
        &CASES_SUITE,
        &EXTERNAL_LIBRARY_SUITE,
        &STANDARD_LIBRARY_SUITE,
        &TYPESCRIPT_SUITE,
    ]
}

fn default_conformance_suites() -> [&'static ConformanceSuite; 3] {
    [
        &CASES_SUITE,
        &EXTERNAL_LIBRARY_SUITE,
        &STANDARD_LIBRARY_SUITE,
    ]
}

fn full_conformance_suites() -> [&'static ConformanceSuite; 4] {
    all_conformance_suites()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TypeRecord {
    path: Arc<str>,
    start: u32,
    end: u32,
    text: String,
    ty_variant: Option<&'static str>,
    ast_kind: Option<&'static str>,
    ty_repr: String,
}

impl TypeRecord {
    fn key(&self) -> TypeRecordKey {
        TypeRecordKey {
            start: self.start,
            end: self.end,
            text: self.text.clone(),
        }
    }

    fn from_tsv(line: &str) -> Result<Self, String> {
        let mut fields = line.splitn(5, '\t');
        let path = Arc::from(fields.next().ok_or("missing path")?);
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
            ty_variant: None,
            ast_kind: None,
            ty_repr: ty,
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
    path: Arc<str>,
    matched_types: usize,
    errors: Vec<ComparisonError>,
}

#[derive(Default)]
struct OxcRecordCollection {
    records: Vec<TypeRecord>,
    panicked_paths: BTreeSet<String>,
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
    panicked_files: usize,
    total_files: usize,
    matched_types: usize,
    mismatched_types: usize,
    total_types: usize,
}

impl ComparisonStats {
    fn from_results(results: &[FileResult], panicked_files: usize) -> Self {
        let total_files = results.len() + panicked_files;
        let failed_files = results.iter().filter(|result| !result.passed()).count();
        let passed_files = results.len() - failed_files;
        let matched_types = results.iter().map(|result| result.matched_types).sum();
        let mismatched_types = results.iter().map(FileResult::mismatched_types).sum();
        let total_types = matched_types + mismatched_types;

        Self {
            passed_files,
            failed_files,
            panicked_files,
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
            "files: {} passed, {} failed, {} panicked, {} total ({:.2}%)\ntypes: {} matched, {} mismatched, {} total ({:.2}%)",
            self.passed_files,
            self.failed_files,
            self.panicked_files,
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

struct ReadyConformanceFile {
    path: PathBuf,
    source_text: String,
}

struct ReadyConformanceBatch {
    files: Vec<ReadyConformanceFile>,
}

struct SharedConformanceCollection {
    worker_count: usize,
    progress: Arc<ConformanceCollectionProgress>,
}

#[derive(Default)]
struct ConformanceCollectionProgressState {
    completed_paths: usize,
    active_paths: BTreeSet<PathBuf>,
}

struct ConformanceCollectionProgress {
    total_paths: usize,
    line_width: usize,
    state: Mutex<ConformanceCollectionProgressState>,
}

impl ConformanceCollectionProgress {
    fn new(total_paths: usize) -> Self {
        Self {
            total_paths,
            line_width: terminal_size()
                .map_or(80, |(Width(width), _)| usize::from(width))
                .saturating_sub(1),
            state: Mutex::new(ConformanceCollectionProgressState::default()),
        }
    }

    fn start(&self, path: &Path) {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        state.active_paths.insert(path.to_path_buf());
        report_collection_progress(&state, self.total_paths, self.line_width);
    }

    fn finish(&self, path: Option<&Path>) {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(path) = path {
            state.active_paths.remove(path);
        }
        state.completed_paths += 1;
        report_collection_progress(&state, self.total_paths, self.line_width);
    }
}

struct ConformanceCollectionTiming {
    enabled: bool,
    started_at: Instant,
    reader_nanos: AtomicU64,
    read_nanos: AtomicU64,
    send_wait_nanos: AtomicU64,
    check_nanos: AtomicU64,
    bytes_read: AtomicUsize,
}

impl ConformanceCollectionTiming {
    fn new() -> Self {
        Self {
            enabled: std::env::var_os("OXC_CONFORMANCE_TIMING").is_some(),
            started_at: Instant::now(),
            reader_nanos: AtomicU64::new(0),
            read_nanos: AtomicU64::new(0),
            send_wait_nanos: AtomicU64::new(0),
            check_nanos: AtomicU64::new(0),
            bytes_read: AtomicUsize::new(0),
        }
    }

    fn is_enabled(&self) -> bool {
        self.enabled
    }

    fn record_read(&self, elapsed: Duration, bytes: usize) {
        if !self.enabled {
            return;
        }

        self.read_nanos
            .fetch_add(duration_nanos(elapsed), Ordering::Relaxed);
        self.bytes_read.fetch_add(bytes, Ordering::Relaxed);
    }

    fn record_send_wait(&self, elapsed: Duration) {
        if self.enabled {
            self.send_wait_nanos
                .fetch_add(duration_nanos(elapsed), Ordering::Relaxed);
        }
    }

    fn record_check(&self, elapsed: Duration) {
        if self.enabled {
            self.check_nanos
                .fetch_add(duration_nanos(elapsed), Ordering::Relaxed);
        }
    }

    fn record_reader(&self, elapsed: Duration) {
        if self.enabled {
            self.reader_nanos
                .store(duration_nanos(elapsed), Ordering::Relaxed);
        }
    }

    fn report(&self, suite: &ConformanceSuite, total_paths: usize, worker_count: usize) {
        if !self.enabled {
            return;
        }

        let wall = self.started_at.elapsed();
        let reader = nanos_duration(self.reader_nanos.load(Ordering::Relaxed));
        let read = nanos_duration(self.read_nanos.load(Ordering::Relaxed));
        let send_wait = nanos_duration(self.send_wait_nanos.load(Ordering::Relaxed));
        let check = nanos_duration(self.check_nanos.load(Ordering::Relaxed));
        let estimated_parallel_check = check.div_f64(worker_count as f64);
        let bytes_read = self.bytes_read.load(Ordering::Relaxed);

        eprintln!(
            "{} collection timing: files={} workers={} bytes_read={} wall={:.3}s reader_wall={:.3}s read_sum={:.3}s send_wait={:.3}s check_sum={:.3}s check_sum/workers={:.3}s",
            suite.name,
            total_paths,
            worker_count,
            bytes_read,
            wall.as_secs_f64(),
            reader.as_secs_f64(),
            read.as_secs_f64(),
            send_wait.as_secs_f64(),
            check.as_secs_f64(),
            estimated_parallel_check.as_secs_f64(),
        );
    }
}

fn duration_nanos(duration: Duration) -> u64 {
    duration.as_nanos().min(u128::from(u64::MAX)) as u64
}

fn nanos_duration(nanos: u64) -> Duration {
    Duration::from_nanos(nanos)
}

struct FixtureProgramHost {
    files: HashMap<PathBuf, String>,
    resolver: ResolverGeneric<FixtureResolverFileSystem>,
    resolver_paths: HashMap<PathBuf, PathBuf>,
}

#[derive(Default)]
struct FixtureResolverFileSystem {
    files: HashMap<PathBuf, Vec<u8>>,
    directories: BTreeSet<PathBuf>,
}

impl FixtureProgramHost {
    fn new(files: &[CompilerTestFile], module_files: bool) -> Self {
        let mut host_files = HashMap::new();
        let mut resolver_files = HashMap::new();
        let mut resolver_paths = HashMap::new();
        let mut directories = BTreeSet::new();

        for file in files {
            let fixture_path = normalize_fixture_path(Path::new(&file.name));
            let resolver_path = resolver_path_for_fixture_path(&fixture_path);
            let parser_source_text = if module_files {
                virtual_module_source_text(&file.source_text)
            } else {
                file.source_text.clone()
            };
            host_files.insert(fixture_path.clone(), parser_source_text.clone());
            resolver_paths.insert(resolver_path.clone(), fixture_path);
            resolver_files.insert(resolver_path.clone(), parser_source_text.into_bytes());
            add_resolver_parent_directories(&mut directories, &resolver_path);
        }

        let resolver = ResolverGeneric::new_with_file_system(
            FixtureResolverFileSystem {
                files: resolver_files,
                directories,
            },
            fixture_resolve_options(),
        );

        Self {
            files: host_files,
            resolver,
            resolver_paths,
        }
    }
}

impl FileSystem for FixtureResolverFileSystem {
    fn new() -> Self {
        Self::default()
    }

    fn read(&self, path: &Path) -> io::Result<Vec<u8>> {
        self.files.get(path).cloned().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!("file not found: {}", path.display()),
            )
        })
    }

    fn read_to_string(&self, path: &Path) -> io::Result<String> {
        string_from_utf8_bytes_simd(self.read(path)?)
    }

    fn metadata(&self, path: &Path) -> io::Result<FileMetadata> {
        if self.files.contains_key(path) {
            return Ok(FileMetadata::new(true, false, false));
        }
        if self.directories.contains(path) {
            return Ok(FileMetadata::new(false, true, false));
        }
        Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("path not found: {}", path.display()),
        ))
    }

    fn symlink_metadata(&self, path: &Path) -> io::Result<FileMetadata> {
        self.metadata(path)
    }

    fn read_link(&self, path: &Path) -> Result<PathBuf, ResolveError> {
        Err(ResolveError::from(io::Error::new(
            io::ErrorKind::NotFound,
            format!("not a symlink: {}", path.display()),
        )))
    }

    fn canonicalize(&self, path: &Path) -> io::Result<PathBuf> {
        let path = normalize_fixture_path(path);
        self.metadata(&path)?;
        Ok(path)
    }
}

fn read_to_string_simd_utf8(path: &Path) -> io::Result<String> {
    string_from_utf8_bytes_simd(std::fs::read(path)?)
}

fn string_from_utf8_bytes_simd(bytes: Vec<u8>) -> io::Result<String> {
    simdutf8::basic::from_utf8(&bytes).map_err(|err| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("invalid UTF-8: {err:?}"),
        )
    })?;

    // SAFETY: simdutf8 validated the complete byte buffer above.
    Ok(unsafe { String::from_utf8_unchecked(bytes) })
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
        let containing_file = resolver_path_for_fixture_path(containing_file);
        match self.resolver.resolve_file(&containing_file, specifier) {
            Ok(resolution) => program::HostModuleResolution::Path(
                self.resolver_paths
                    .get(resolution.path())
                    .cloned()
                    .unwrap_or_else(|| fixture_path_for_resolver_path(resolution.path())),
            ),
            Err(ResolveError::Builtin { resolved, .. }) => {
                program::HostModuleResolution::Builtin(resolved)
            }
            Err(ResolveError::NotFound(_)) if is_bare_specifier(specifier) => {
                program::HostModuleResolution::External(specifier.to_string())
            }
            Err(ResolveError::NotFound(_)) => {
                program::HostModuleResolution::Missing(specifier.to_string())
            }
            Err(error) => program::HostModuleResolution::Missing(error.to_string()),
        }
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

type ConformanceResult<T = ()> = Result<T, ConformanceError>;

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
        text: String,
        expected: String,
        actual: String,
    },
    MissingFromOxc {
        start: u32,
        text: String,
        expected: String,
    },
    ExtraInOxc {
        start: u32,
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

#[cfg(feature = "conformance-tsc")]
#[test]
fn external_library_type_extractor() -> ConformanceResult {
    extract_tsc_type_records(&EXTERNAL_LIBRARY_SUITE)
}

#[cfg(feature = "conformance-tsc")]
#[test]
fn standard_library_type_extractor() -> ConformanceResult {
    extract_tsc_type_records(&STANDARD_LIBRARY_SUITE)
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

#[cfg(feature = "conformance")]
#[test]
fn external_library_type_records() -> ConformanceResult {
    run_type_record_conformance_on_thread("external_library_type_records", &EXTERNAL_LIBRARY_SUITE)
}

#[cfg(feature = "conformance")]
#[test]
fn standard_library_type_records() -> ConformanceResult {
    run_type_record_conformance_on_thread("standard_library_type_records", &STANDARD_LIBRARY_SUITE)
}

#[cfg(feature = "conformance")]
#[test]
fn full_conformance() -> ConformanceResult {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let target = conformance_target_argument(&repo_root)?;
    if let Some(case_path) = target.case_path {
        return run_single_file_conformance_on_thread(
            "full_conformance",
            case_path,
            target.refresh_tsc,
        );
    }

    let mut failures = Vec::new();
    let mut suites = Vec::new();

    for suite in target.suites {
        if target.refresh_tsc
            && let Err(err) = refresh_tsc_type_records(suite)
        {
            failures.push(format!(
                "{} TypeScript record refresh failed:\n{}",
                suite.name,
                err.into_message()
            ));
            continue;
        }

        suites.push(suite);
    }

    for (suite, result) in run_type_record_conformance_suites(&suites) {
        if let Err(err) = result {
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

fn run_type_record_conformance_suites(
    suites: &[&'static ConformanceSuite],
) -> Vec<(&'static ConformanceSuite, ConformanceResult)> {
    if suites.len() <= 1 {
        return suites
            .iter()
            .map(|&suite| {
                (
                    suite,
                    run_type_record_conformance_on_thread("full_conformance", suite),
                )
            })
            .collect();
    }

    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let total_paths = suites
        .iter()
        .map(|suite| discover_compiler_cases(suite, &repo_root.join(suite.cases_root)).len())
        .sum();
    let worker_count = conformance_worker_count(total_paths);
    let shared = SharedConformanceCollection {
        worker_count,
        progress: Arc::new(ConformanceCollectionProgress::new(total_paths)),
    };
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(worker_count)
        .stack_size(CONFORMANCE_THREAD_STACK_SIZE)
        .thread_name(|worker_index| format!("conformance-worker-{worker_index}"))
        .build()
        .unwrap_or_else(|err| panic!("failed to build conformance worker pool: {err}"));

    pool.install(|| {
        suites
            .par_iter()
            .map(|&suite| (suite, run_type_record_conformance(suite, Some(&shared))))
            .collect()
    })
}

struct ConformanceTarget {
    case_path: Option<PathBuf>,
    suites: Vec<&'static ConformanceSuite>,
    refresh_tsc: bool,
}

fn conformance_target_argument(repo_root: &Path) -> ConformanceResult<ConformanceTarget> {
    conformance_target_from_arguments(repo_root, std::env::args_os().skip(1))
}

fn conformance_target_from_arguments(
    repo_root: &Path,
    arguments: impl IntoIterator<Item = std::ffi::OsString>,
) -> ConformanceResult<ConformanceTarget> {
    let mut case_paths = Vec::new();
    let mut suites = Vec::new();
    let mut refresh_tsc = false;
    for argument in arguments {
        if argument == "refresh-tsc"
            || argument == "--refresh-tsc"
            || argument == "update-tsc"
            || argument == "--update-tsc"
        {
            refresh_tsc = true;
            continue;
        }

        if let Some(argument) = argument.to_str()
            && conformance_test_harness_argument(argument)
        {
            continue;
        }

        let path = PathBuf::from(&argument);
        if is_supported_case_extension(&path) {
            let candidate = if path.is_absolute() {
                path
            } else {
                repo_root.join(path)
            };
            let case_path = candidate.canonicalize().map_err(|err| {
                ConformanceError::new(format!(
                    "failed to resolve conformance case {}: {err}",
                    candidate.display()
                ))
            })?;
            case_paths.push(case_path);
            continue;
        }

        if let Some(argument) = argument.to_str()
            && let Some(suite) = conformance_suite_for_argument(argument)
        {
            suites.push(suite);
            continue;
        }

        if let Some(argument) = argument.to_str()
            && conformance_full_argument(argument)
        {
            suites.extend(full_conformance_suites());
            continue;
        }

        return Err(ConformanceError::new(format!(
            "unknown conformance target argument: {}",
            argument.to_string_lossy()
        )));
    }

    let case_path = match case_paths.len() {
        0 => None,
        1 => case_paths.pop(),
        _ => Err(ConformanceError::new(format!(
            "expected at most one conformance case path, got {}",
            case_paths.len()
        )))?,
    };

    if case_path.is_some() && !suites.is_empty() {
        return Err(ConformanceError::new(
            "expected either a conformance case path or a suite name, not both".to_string(),
        ));
    }

    if suites.is_empty() {
        suites.extend(default_conformance_suites());
    }

    Ok(ConformanceTarget {
        case_path,
        suites,
        refresh_tsc,
    })
}

fn conformance_suite_for_argument(argument: &str) -> Option<&'static ConformanceSuite> {
    match argument {
        "cases" | "local" => Some(&CASES_SUITE),
        "external" | "libraries" | "library" => Some(&EXTERNAL_LIBRARY_SUITE),
        "lib" | "libs" | "stdlib" | "standard-library" => Some(&STANDARD_LIBRARY_SUITE),
        "typescript" | "ts" | "upstream" => Some(&TYPESCRIPT_SUITE),
        _ => None,
    }
}

fn conformance_full_argument(argument: &str) -> bool {
    matches!(argument, "all" | "full")
}

fn conformance_test_harness_argument(argument: &str) -> bool {
    matches!(
        argument,
        "conformance::full_conformance" | "--exact" | "--nocapture"
    )
}

fn is_supported_case_extension(path: &Path) -> bool {
    path.extension()
        .is_some_and(|extension| extension == "ts" || extension == "tsx")
}

fn run_type_record_conformance_on_thread(
    test_name: &'static str,
    suite: &'static ConformanceSuite,
) -> ConformanceResult {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(CONFORMANCE_THREAD_STACK_SIZE)
        .spawn(move || run_type_record_conformance(suite, None))
        .map_err(|err| {
            ConformanceError::new(format!("failed to spawn conformance test thread: {err}"))
        })?
        .join()
        .map_err(thread_panic_error)?
}

fn run_single_file_conformance_on_thread(
    test_name: &'static str,
    case_path: PathBuf,
    refresh_tsc: bool,
) -> ConformanceResult {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(CONFORMANCE_THREAD_STACK_SIZE)
        .spawn(move || run_single_file_conformance(&case_path, refresh_tsc))
        .map_err(|err| {
            ConformanceError::new(format!("failed to spawn conformance test thread: {err}"))
        })?
        .join()
        .map_err(thread_panic_error)?
}

#[cfg(feature = "conformance-tsc")]
fn extract_tsc_type_records(suite: &ConformanceSuite) -> ConformanceResult {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cases_root = repo_root.join(suite.cases_root);
    let tsc_types_path = repo_root.join(suite.tsc_types_path);

    ensure_cases_root(suite, &cases_root)?;
    run_tsc_extractor(&repo_root, suite, &cases_root, &tsc_types_path)?;
    Ok(())
}

#[cfg(feature = "conformance-tsc")]
fn refresh_tsc_type_records(suite: &ConformanceSuite) -> ConformanceResult {
    extract_tsc_type_records(suite)
}

#[cfg(not(feature = "conformance-tsc"))]
fn refresh_tsc_type_records(_suite: &ConformanceSuite) -> ConformanceResult {
    Err(ConformanceError::new(
        "refresh-tsc requires the conformance-tsc feature; use `cargo conformance-refresh`",
    ))
}

#[cfg(feature = "conformance-tsc")]
fn extract_tsc_type_records_for_case(
    repo_root: &Path,
    suite: &ConformanceSuite,
    cases_root: &Path,
    case_path: &Path,
) -> ConformanceResult<Vec<TypeRecord>> {
    ensure_cases_root(suite, cases_root)?;
    let output = run_tsc_extractor_to_stdout(repo_root, suite, cases_root, case_path)?;
    parse_records(&output, "TypeScript extractor stdout")
}

#[cfg(feature = "conformance-tsc")]
fn refresh_tsc_type_records_for_case(
    repo_root: &Path,
    suite: &ConformanceSuite,
    cases_root: &Path,
    case_path: &Path,
) -> ConformanceResult<Vec<TypeRecord>> {
    extract_tsc_type_records_for_case(repo_root, suite, cases_root, case_path)
}

#[cfg(not(feature = "conformance-tsc"))]
fn refresh_tsc_type_records_for_case(
    _repo_root: &Path,
    _suite: &ConformanceSuite,
    _cases_root: &Path,
    _case_path: &Path,
) -> ConformanceResult<Vec<TypeRecord>> {
    Err(ConformanceError::new(
        "refresh-tsc requires the conformance-tsc feature; use `cargo conformance-refresh`",
    ))
}

fn run_single_file_conformance(case_path: &Path, refresh_tsc: bool) -> ConformanceResult {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let (suite, cases_root) = suite_for_case_path(&repo_root, case_path)?;

    let tsc_records = if refresh_tsc {
        refresh_tsc_type_records_for_case(&repo_root, suite, &cases_root, case_path)?
    } else {
        read_tsc_records_for_case(&repo_root, suite, &cases_root, case_path)?
    };
    let collected = collect_oxc_records_for_case(&cases_root, case_path)?;
    let tsc_records = filter_panicked_records(tsc_records, &collected.panicked_paths);
    let oxc_records = filter_panicked_records(collected.records, &collected.panicked_paths);
    let results = compare_records(&tsc_records, &oxc_records);
    let stats = ComparisonStats::from_results(&results, collected.panicked_paths.len());
    print!("{}", format_type_record_report(suite, &stats, &results));

    let summary = stats.summary();
    if stats.failed_files == 0 {
        eprintln!(
            "{} single-file type-record conformance passed:\n{summary}",
            suite.name
        );
        Ok(())
    } else {
        Err(ConformanceError::new(format!(
            "{} single-file type-record conformance failed:\n{summary}",
            suite.name
        )))
    }
}

fn suite_for_case_path(
    repo_root: &Path,
    case_path: &Path,
) -> ConformanceResult<(&'static ConformanceSuite, PathBuf)> {
    for suite in all_conformance_suites() {
        let cases_root = repo_root
            .join(suite.cases_root)
            .canonicalize()
            .map_err(|err| {
                ConformanceError::new(format!(
                    "failed to resolve {} root {}: {err}",
                    suite.name, suite.cases_root
                ))
            })?;

        if !case_path.starts_with(&cases_root) {
            continue;
        }

        let relative = relative_path(&cases_root, case_path);
        if suite.compiler_cases_only && relative != "compiler" && !relative.starts_with("compiler/")
        {
            continue;
        }
        return Ok((suite, cases_root));
    }

    let roots = all_conformance_suites()
        .map(|suite| suite.cases_root)
        .join(", ");
    Err(ConformanceError::new(format!(
        "conformance case must be under one of {roots}: {}",
        case_path.display()
    )))
}

fn run_type_record_conformance(
    suite: &ConformanceSuite,
    shared: Option<&SharedConformanceCollection>,
) -> ConformanceResult {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cases_root = repo_root.join(suite.cases_root);
    let tsc_types_path = repo_root.join(suite.tsc_types_path);
    let snapshot_path = repo_root.join(suite.snapshot_path);

    ensure_cases_root(suite, &cases_root)?;

    let collected = collect_oxc_records(suite, &cases_root, shared);
    let tsc_records =
        filter_panicked_records(read_records(&tsc_types_path)?, &collected.panicked_paths);
    let oxc_records = filter_panicked_records(collected.records, &collected.panicked_paths);
    write_type_outputs(suite, &cases_root, &oxc_records, &tsc_records);
    let results = compare_records(&tsc_records, &oxc_records);
    let stats = ComparisonStats::from_results(&results, collected.panicked_paths.len());
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

#[cfg(feature = "conformance-tsc")]
fn run_tsc_extractor(
    repo_root: &Path,
    suite: &ConformanceSuite,
    cases_root: &Path,
    out_path: &Path,
) -> ConformanceResult {
    let extractor_path = repo_root.join("tests/conformance/tsc_type_extractor.ts");
    let case_discovery = if suite.compiler_cases_only {
        "compiler"
    } else {
        "all"
    };
    let output = std::process::Command::new("node")
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

#[cfg(feature = "conformance-tsc")]
fn run_tsc_extractor_to_stdout(
    repo_root: &Path,
    suite: &ConformanceSuite,
    cases_root: &Path,
    case_path: &Path,
) -> ConformanceResult<String> {
    let extractor_path = repo_root.join("tests/conformance/tsc_type_extractor.ts");
    let case_discovery = if suite.compiler_cases_only {
        "compiler"
    } else {
        "all"
    };
    let output = std::process::Command::new("node")
        .arg(&extractor_path)
        .arg("--repo-root")
        .arg(repo_root)
        .arg("--cases-root")
        .arg(cases_root)
        .arg("--case-discovery")
        .arg(case_discovery)
        .arg("--case")
        .arg(case_path)
        .arg("--out")
        .arg("-")
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

    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
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

fn collect_oxc_records(
    suite: &ConformanceSuite,
    cases_root: &Path,
    shared: Option<&SharedConformanceCollection>,
) -> OxcRecordCollection {
    let paths = discover_compiler_cases(suite, cases_root);
    let total_paths = paths.len();
    let worker_count = shared.map_or_else(
        || conformance_worker_count(total_paths),
        |shared| shared.worker_count,
    );

    if total_paths == 0 {
        return OxcRecordCollection::default();
    }

    let progress = shared.map_or_else(
        || Arc::new(ConformanceCollectionProgress::new(total_paths)),
        |shared| Arc::clone(&shared.progress),
    );
    let timing = Arc::new(ConformanceCollectionTiming::new());
    let (ready_sender, ready_receiver) =
        mpsc::sync_channel(conformance_read_ahead_capacity(worker_count));
    let reader_progress = Arc::clone(&progress);
    let reader_timing = Arc::clone(&timing);
    let reader = std::thread::Builder::new()
        .name("conformance-reader".to_string())
        .spawn(move || {
            let reader_started_at = reader_timing.is_enabled().then(Instant::now);
            let mut ready_files = Vec::new();
            for path in paths {
                let read_started_at = reader_timing.is_enabled().then(Instant::now);
                let source_text = match read_to_string_simd_utf8(&path) {
                    Ok(source_text) => source_text,
                    Err(_) => {
                        reader_progress.finish(None);
                        continue;
                    }
                };
                if let Some(read_started_at) = read_started_at {
                    reader_timing.record_read(read_started_at.elapsed(), source_text.len());
                }

                ready_files.push(ReadyConformanceFile { path, source_text });
            }

            let batch_count = conformance_batch_count(ready_files.len(), worker_count);
            for batch in balance_conformance_batches(ready_files, batch_count) {
                let send_started_at = reader_timing.is_enabled().then(Instant::now);
                if ready_sender.send(batch).is_err() {
                    break;
                }
                if let Some(send_started_at) = send_started_at {
                    reader_timing.record_send_wait(send_started_at.elapsed());
                }
            }
            if let Some(reader_started_at) = reader_started_at {
                reader_timing.record_reader(reader_started_at.elapsed());
            }
        })
        .unwrap_or_else(|err| panic!("failed to spawn conformance reader thread: {err}"));

    let collect_records = || {
        let timing = Arc::clone(&timing);
        let progress = Arc::clone(&progress);
        ready_receiver
            .into_iter()
            .par_bridge()
            .map(|ready_batch| {
                let allocator = Allocator::default();
                let prepared_programs = program::PreparedProgramSet::embedded_libraries(&allocator)
                    .unwrap_or_else(|err| panic!("failed to prepare embedded libraries: {err}"));
                let mut batch_collection = OxcRecordCollection::default();
                for ready_file in ready_batch.files {
                    progress.start(&ready_file.path);
                    let check_started_at = timing.is_enabled().then(Instant::now);
                    let collection = collect_oxc_records_from_source_with_programs(
                        cases_root,
                        &ready_file.path,
                        &ready_file.source_text,
                        &allocator,
                        Some(&prepared_programs),
                    );
                    batch_collection.records.extend(collection.records);
                    batch_collection
                        .panicked_paths
                        .extend(collection.panicked_paths);
                    if let Some(check_started_at) = check_started_at {
                        timing.record_check(check_started_at.elapsed());
                    }
                    progress.finish(Some(&ready_file.path));
                }
                batch_collection
            })
            .collect::<Vec<_>>()
            .into_iter()
            .fold(OxcRecordCollection::default(), |mut collection, batch| {
                collection.records.extend(batch.records);
                collection.panicked_paths.extend(batch.panicked_paths);
                collection
            })
    };
    let mut collection = if shared.is_some() {
        collect_records()
    } else {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(worker_count)
            .stack_size(CONFORMANCE_THREAD_STACK_SIZE)
            .thread_name(|worker_index| format!("conformance-worker-{worker_index}"))
            .build()
            .unwrap_or_else(|err| panic!("failed to build conformance worker pool: {err}"));
        pool.install(collect_records)
    };

    reader
        .join()
        .unwrap_or_else(|payload| panic!("{}", thread_panic_error(payload).into_message()));

    eprintln!();
    timing.report(suite, total_paths, worker_count);
    collection.records.sort_by(|left, right| {
        left.path
            .cmp(&right.path)
            .then_with(|| left.start.cmp(&right.start))
            .then_with(|| left.end.cmp(&right.end))
            .then_with(|| left.text.cmp(&right.text))
            .then_with(|| left.ty_repr.cmp(&right.ty_repr))
    });
    collection
}

fn balance_conformance_batches(
    mut files: Vec<ReadyConformanceFile>,
    batch_count: usize,
) -> Vec<ReadyConformanceBatch> {
    files.sort_unstable_by_key(|file| std::cmp::Reverse(file.source_text.len()));
    let mut batches = (0..batch_count.min(files.len()))
        .map(|_| (0_usize, Vec::new()))
        .collect::<Vec<_>>();
    for file in files {
        let (size, batch) = batches
            .iter_mut()
            .min_by_key(|(size, _)| *size)
            .expect("at least one conformance batch");
        *size += file.source_text.len();
        batch.push(file);
    }
    batches
        .into_iter()
        .map(|(_, files)| ReadyConformanceBatch { files })
        .collect()
}

fn conformance_batch_count(file_count: usize, worker_count: usize) -> usize {
    file_count
        .div_ceil(MIN_FILES_PER_PREPARED_BATCH)
        .min(worker_count)
}

fn conformance_read_ahead_capacity(worker_count: usize) -> usize {
    worker_count.saturating_mul(2).max(1)
}

fn conformance_worker_count(total_paths: usize) -> usize {
    if total_paths == 0 {
        return 0;
    }

    std::env::var("OXC_CONFORMANCE_WORKERS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|&count| count > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, usize::from))
        .min(total_paths)
}

fn report_collection_progress(
    state: &ConformanceCollectionProgressState,
    total: usize,
    line_width: usize,
) {
    use std::io::Write as _;

    let mut stderr = io::stderr().lock();
    let line = format_collection_progress(state, total, line_width);
    let _ = write!(stderr, "\r\x1b[2K{line}");
    let _ = stderr.flush();
}

fn format_collection_progress(
    state: &ConformanceCollectionProgressState,
    total: usize,
    line_width: usize,
) -> String {
    let mut line = format!("collecting {}/{total}", state.completed_paths);
    if state.active_paths.is_empty() || line.len() >= line_width {
        return truncate_progress_text(&line, line_width);
    }

    line.push_str(" [");
    let active_paths = state.active_paths.iter().collect::<Vec<_>>();
    let mut shown = 0;
    for path in &active_paths {
        let name = path
            .file_name()
            .unwrap_or(path.as_os_str())
            .to_string_lossy();
        let delimiter = if shown == 0 { "" } else { ", " };
        let hidden_after = active_paths.len() - shown - 1;
        let suffix = if hidden_after == 0 {
            "]".to_string()
        } else {
            format!(", +{hidden_after}]")
        };

        if line.len() + delimiter.len() + name.len() + suffix.len() <= line_width {
            line.push_str(delimiter);
            line.push_str(&name);
            shown += 1;
            if shown == active_paths.len() {
                line.push(']');
            }
            continue;
        }

        if shown == 0 {
            let available = line_width.saturating_sub(line.len() + suffix.len());
            line.push_str(&truncate_progress_text(&name, available));
            line.push_str(&suffix);
        } else {
            line.push_str(&format!(", +{}]", active_paths.len() - shown));
        }
        break;
    }
    truncate_progress_text(&line, line_width)
}

fn truncate_progress_text(text: &str, width: usize) -> String {
    if text.len() <= width {
        return text.to_string();
    }
    if width <= 3 {
        return ".".repeat(width);
    }
    format!("{}...", &text[..width - 3])
}

fn collect_oxc_records_for_case(
    cases_root: &Path,
    case_path: &Path,
) -> ConformanceResult<OxcRecordCollection> {
    let source_text = read_to_string_simd_utf8(case_path).map_err(|err| {
        ConformanceError::new(format!(
            "failed to read conformance case {}: {err}",
            case_path.display()
        ))
    })?;
    let allocator = Allocator::default();
    let mut collection = collect_oxc_records_from_source_with_programs(
        cases_root,
        case_path,
        &source_text,
        &allocator,
        None,
    );
    collection.records.sort_by(|left, right| {
        left.path
            .cmp(&right.path)
            .then_with(|| left.start.cmp(&right.start))
            .then_with(|| left.end.cmp(&right.end))
            .then_with(|| left.text.cmp(&right.text))
            .then_with(|| left.ty_repr.cmp(&right.ty_repr))
    });
    Ok(collection)
}

fn read_tsc_records_for_case(
    repo_root: &Path,
    suite: &ConformanceSuite,
    cases_root: &Path,
    case_path: &Path,
) -> ConformanceResult<Vec<TypeRecord>> {
    let relative_path = relative_path(cases_root, case_path);
    let tsc_records_path = repo_root.join(suite.tsc_types_path);
    Ok(read_records(&tsc_records_path)?
        .into_iter()
        .filter(|record| {
            record.path.as_ref() == relative_path
                || record
                    .path
                    .strip_prefix(relative_path.as_str())
                    .is_some_and(|suffix| suffix.starts_with("::"))
        })
        .collect())
}

fn collect_oxc_records_from_source(
    cases_root: &Path,
    path: &Path,
    source_text: &str,
) -> Vec<TypeRecord> {
    let allocator = Allocator::default();
    collect_oxc_records_from_source_with_programs(cases_root, path, source_text, &allocator, None)
        .records
}

fn panicked_record_path(
    error: &program::ProgramStoreError,
    relative_path: &str,
    compiler_case: &CompilerTestCase,
) -> Option<String> {
    let program::ProgramStoreError::Parse { path, .. } = error else {
        return None;
    };

    compiler_case.files.iter().find_map(|source_file| {
        let source_path = normalize_fixture_path(Path::new(&source_file.name));
        (source_path == *path)
            .then(|| record_path(relative_path, source_file, compiler_case.has_explicit_files))
    })
}

fn collect_oxc_records_from_source_with_programs<'a>(
    cases_root: &Path,
    path: &Path,
    source_text: &str,
    allocator: &'a Allocator,
    prepared_programs: Option<&'a program::PreparedProgramSet<'a>>,
) -> OxcRecordCollection {
    let relative_path = relative_path(cases_root, path);
    let compiler_case = parse_compiler_test_case(source_text, &relative_path);
    let _settings = &compiler_case.settings;
    let mut collection = OxcRecordCollection::default();
    let parsed = match parse_fixture_program(allocator, &compiler_case, prepared_programs) {
        Ok(parsed) => Some(parsed),
        Err(error) => {
            if let Some(path) = panicked_record_path(&error, &relative_path, &compiler_case) {
                collection.panicked_paths.insert(path);
            }
            None
        }
    };
    if let Some(parsed) = parsed {
        let checker = CheckerBuilder::new().build(&parsed.store);
        for source_file in &compiler_case.files {
            let _file_settings = &source_file.settings;
            let Some(program_id) = parsed
                .store
                .id_for_path(&normalize_fixture_path(Path::new(&source_file.name)))
            else {
                continue;
            };
            collection.records.extend(actual_identifier_records(
                &checker,
                program_id,
                &record_path(
                    &relative_path,
                    source_file,
                    compiler_case.has_explicit_files,
                ),
                &source_file.source_text,
            ));
        }
        return collection;
    }

    // Some conformance fixtures are intentionally broken or use unsupported syntax/features.
    // Fall back to per-file extraction so we still emit records for parsable files.
    for source_file in &compiler_case.files {
        let parsed = match parse_single_fixture_program(
            allocator,
            source_file,
            compiler_case.has_explicit_files,
            prepared_programs,
        ) {
            Ok(parsed) => parsed,
            Err(error) => {
                if let Some(path) = panicked_record_path(&error, &relative_path, &compiler_case) {
                    collection.panicked_paths.insert(path);
                }
                continue;
            }
        };
        let Some(program_id) = parsed
            .store
            .id_for_path(&normalize_fixture_path(Path::new(&source_file.name)))
        else {
            continue;
        };
        let checker = CheckerBuilder::new().build(&parsed.store);
        collection.records.extend(actual_identifier_records(
            &checker,
            program_id,
            &record_path(
                &relative_path,
                source_file,
                compiler_case.has_explicit_files,
            ),
            &source_file.source_text,
        ));
    }

    collection
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
    // Some TS test cases contain byte order marks (BOM) at the beginning of the file.
    let comment = line
        .trim_start_matches('\u{feff}')
        .trim_start()
        .strip_prefix("//")?
        .trim_start();
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

fn is_compilable_fixture_file(path: &Path) -> bool {
    let file_name = path.file_name().and_then(|file_name| file_name.to_str());
    let extension = path.extension().and_then(|extension| extension.to_str());
    file_name.is_some_and(|file_name| file_name.ends_with(".d.ts"))
        || matches!(
            extension,
            Some("ts" | "tsx" | "js" | "jsx" | "mjs" | "cjs" | "mts" | "cts")
        )
}

fn fixture_resolve_options() -> ResolveOptions {
    let mut options = program::ts_resolve_options();
    options.cwd = Some(fixture_resolver_root());
    options.main_fields = ["types", "typings", "main"]
        .into_iter()
        .map(str::to_string)
        .collect();
    options.symlinks = false;
    options
}

fn fixture_resolver_root() -> PathBuf {
    PathBuf::from("/__oxc_checker_fixture__")
}

fn resolver_path_for_fixture_path(path: &Path) -> PathBuf {
    let mut resolver_path = fixture_resolver_root();
    for component in normalize_fixture_path(path).components() {
        match component {
            Component::CurDir | Component::RootDir => {}
            Component::ParentDir => {
                resolver_path.pop();
            }
            Component::Prefix(prefix) => resolver_path.push(prefix.as_os_str()),
            Component::Normal(part) => resolver_path.push(part),
        }
    }
    resolver_path
}

fn fixture_path_for_resolver_path(path: &Path) -> PathBuf {
    path.strip_prefix(fixture_resolver_root())
        .map_or_else(|_| normalize_fixture_path(path), normalize_fixture_path)
}

fn add_resolver_parent_directories(directories: &mut BTreeSet<PathBuf>, path: &Path) {
    let mut current = path.parent();
    while let Some(directory) = current {
        directories.insert(normalize_fixture_path(directory));
        let parent = directory.parent();
        if parent == current {
            break;
        }
        current = parent;
    }
}

fn is_bare_specifier(specifier: &str) -> bool {
    !(specifier.is_empty() || specifier.starts_with('.') || specifier.starts_with('/'))
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
    prepared_programs: Option<&'a program::PreparedProgramSet<'a>>,
) -> program::ProgramStoreResult<ParsedFixture<'a>> {
    let host = FixtureProgramHost::new(&compiler_case.files, compiler_case.has_explicit_files);
    let mut builder = program::ProgramStoreBuilder::new(allocator, host);
    if let Some(prepared_programs) = prepared_programs {
        builder = builder.with_prepared_programs(prepared_programs);
    }
    if compiler_case
        .settings
        .get("nolib")
        .is_some_and(|value| compiler_directive_bool(value))
    {
        builder = builder.without_default_lib();
    } else if let Some(lib) = compiler_case.settings.get("lib") {
        builder = builder.with_lib_names(parse_compiler_lib_names(lib));
    } else if let Some(target) = compiler_case.settings.get("target") {
        builder = builder.with_default_lib_target_name(target)?;
    } else {
        builder = builder.with_default_lib_target_name("esnext")?;
    }
    for source_file in &compiler_case.files {
        if !is_compilable_fixture_file(Path::new(&source_file.name)) {
            continue;
        }
        builder = builder.add_root_file(normalize_fixture_path(Path::new(&source_file.name)));
    }
    let store = builder.build()?;

    Ok(ParsedFixture { store })
}

fn compiler_directive_bool(value: &str) -> bool {
    value.trim().eq_ignore_ascii_case("true")
}

fn parse_compiler_lib_names(value: &str) -> Vec<String> {
    value
        .split(',')
        .map(str::trim)
        .filter(|item| !item.is_empty())
        .map(ToString::to_string)
        .collect()
}

fn parse_single_fixture_program<'a>(
    allocator: &'a Allocator,
    source_file: &CompilerTestFile,
    module_file: bool,
    prepared_programs: Option<&'a program::PreparedProgramSet<'a>>,
) -> program::ProgramStoreResult<ParsedFixture<'a>> {
    let compiler_case = CompilerTestCase {
        settings: HashMap::new(),
        files: vec![CompilerTestFile {
            name: source_file.name.clone(),
            source_text: source_file.source_text.clone(),
            settings: source_file.settings.clone(),
        }],
        has_explicit_files: module_file,
    };
    parse_fixture_program(allocator, &compiler_case, prepared_programs)
}

fn virtual_module_source_text(source_text: &str) -> String {
    let mut module_source_text =
        String::with_capacity(source_text.len() + VIRTUAL_MODULE_MARKER.len());
    module_source_text.push_str(source_text);
    module_source_text.push_str(VIRTUAL_MODULE_MARKER);
    module_source_text
}

fn actual_identifier_records<'a>(
    checker: &CheckerReturn<'a, '_>,
    program_id: program::ProgramId,
    path: &str,
    source_text: &str,
) -> Vec<TypeRecord> {
    let entry = checker.store.entry(program_id).unwrap();
    let path = Arc::<str>::from(path);
    let mut records = entry
        .semantic()
        .nodes()
        .iter_enumerated()
        .filter_map(|(node_id, node)| {
            actual_identifier_record(
                checker,
                checker.arena,
                entry,
                &path,
                source_text,
                node_id,
                node.kind(),
            )
        })
        .collect::<Vec<_>>();
    records.extend(actual_export_specifier_records(
        checker,
        checker.arena,
        &records,
        entry,
        &path,
    ));
    records
}

fn actual_export_specifier_records<'a>(
    checker: &impl Checker<'a>,
    arena: CheckerArena<'a>,
    existing_records: &[TypeRecord],
    entry: &program::ProgramEntry<'a>,
    path: &Arc<str>,
) -> Vec<TypeRecord> {
    let program_id = entry.id();
    let existing_keys = existing_records
        .iter()
        .map(TypeRecord::key)
        .collect::<BTreeSet<_>>();
    entry
        .module_record()
        .local_export_entries
        .iter()
        .filter_map(|export_entry| {
            let ExportLocalName::Name(local_name) = &export_entry.local_name else {
                return None;
            };
            let key = TypeRecordKey {
                start: local_name.span.start,
                end: local_name.span.end,
                text: sanitize_cow(Cow::Borrowed(local_name.name.as_str())),
            };
            if existing_keys.contains(&key) {
                return None;
            }
            let node_ref = export_specifier_node_ref(program_id, entry, export_entry)?;
            let ty = checker.get_type_at_location(node_ref);
            if ty.is_none() {
                return None;
            }
            let ty_variant = ty.enum_variant_name(arena);
            let ty_repr = checker.type_to_string(ty, node_ref);
            Some(TypeRecord {
                path: Arc::clone(path),
                start: key.start,
                end: key.end,
                text: key.text,
                ty_variant: Some(ty_variant),
                ast_kind: Some("ExportSpecifier"),
                ty_repr: sanitize_owned(ty_repr),
            })
        })
        .collect()
}

fn export_specifier_node_ref<'a>(
    program_id: program::ProgramId,
    entry: &program::ProgramEntry<'a>,
    export_entry: &ExportEntry<'a>,
) -> Option<NodeRef> {
    let ExportLocalName::Name(local_name) = &export_entry.local_name else {
        return None;
    };
    entry.program().body.iter().find_map(|statement| {
        let Statement::ExportNamedDeclaration(declaration) = statement else {
            return None;
        };
        if declaration.span != export_entry.statement_span {
            return None;
        }
        declaration.specifiers.iter().find_map(|specifier| {
            let (span, _) = module_export_name_span_and_text(&specifier.local)?;
            (span == local_name.span).then(|| NodeRef::new(program_id, specifier.node_id()))
        })
    })
}

fn actual_identifier_record<'a>(
    checker: &impl Checker<'a>,
    arena: CheckerArena<'a>,
    entry: &program::ProgramEntry<'a>,
    path: &Arc<str>,
    source_text: &str,
    node_id: NodeId,
    kind: AstKind<'a>,
) -> Option<TypeRecord> {
    let program_id = entry.id();
    let node_ref = NodeRef::new(program_id, node_id);
    let (span, text, ty): (Span, Cow<'_, str>, Ty<'_>) = match kind {
        AstKind::BindingIdentifier(_)
            if matches!(
                entry.semantic().nodes().parent_kind(node_id),
                AstKind::TSTypeAliasDeclaration(_)
            ) =>
        {
            return None;
        }
        AstKind::BindingIdentifier(identifier) => (
            identifier.span,
            Cow::Borrowed(identifier.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::IdentifierReference(identifier) => (
            identifier.span,
            Cow::Borrowed(identifier.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::IdentifierName(identifier) => {
            let ty = checker.get_type_at_location(node_ref);
            if ty.is_none() {
                return None;
            }
            (identifier.span, Cow::Borrowed(identifier.name.as_str()), ty)
        }
        AstKind::TSPropertySignature(property) => {
            let (span, text) = identifier_property_key_span_and_text(&property.key)?;
            (
                span,
                Cow::Borrowed(text),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::ObjectProperty(property) => {
            let (span, text) = identifier_property_key_span_and_text(&property.key)?;
            (
                span,
                Cow::Borrowed(text),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::StaticMemberExpression(member) => (
            member.property.span,
            Cow::Borrowed(member.property.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::MethodDefinition(method) => {
            if method.kind == MethodDefinitionKind::Constructor {
                return None;
            }
            let (span, text) = identifier_property_key_span_and_text(&method.key)?;
            (
                span,
                Cow::Borrowed(text),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::TSMethodSignature(method) => {
            let (span, text) = identifier_property_key_span_and_text(&method.key)?;
            (
                span,
                Cow::Borrowed(text),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::ExportSpecifier(specifier) => {
            let (span, text) = module_export_name_span_and_text(&specifier.local)?;
            (
                span,
                Cow::Borrowed(text),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::TSThisParameter(parameter) => (
            parameter.this_span,
            Cow::Borrowed("this"),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::PropertyDefinition(property) => {
            let (span, text) = identifier_property_key_span_and_text(&property.key)?;
            (
                span,
                Cow::Borrowed(text),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::TSTypeAliasDeclaration(alias) => (
            alias.id.span,
            Cow::Borrowed(alias.id.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::TSImportEqualsDeclaration(import_equals) => (
            import_equals.id.span,
            Cow::Borrowed(import_equals.id.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::TSInterfaceDeclaration(interface) => (
            interface.id.span,
            Cow::Borrowed(interface.id.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::TSEnumDeclaration(declaration) => (
            declaration.id.span,
            Cow::Borrowed(declaration.id.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::TSEnumMember(member) => (
            member.id.span(),
            Cow::Owned(member.id.static_name().to_string()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::TSModuleDeclaration(module) => {
            let (span, text) = ts_module_declaration_name_span_and_text(&module.id)?;
            (
                span,
                Cow::Borrowed(text),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::TSTypeParameter(parameter) => (
            parameter.name.span,
            Cow::Borrowed(parameter.name.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::TSMappedType(mapped) => (
            mapped.key.span,
            Cow::Borrowed(mapped.key.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::TSClassImplements(implements) => {
            let (span, text) = ts_type_name_span_and_text(&implements.expression)?;
            (span, text, checker.get_type_at_location(node_ref))
        }
        AstKind::TSInterfaceHeritage(heritage) => {
            let Expression::Identifier(identifier) = &heritage.expression else {
                return None;
            };
            (
                identifier.span,
                Cow::Borrowed(identifier.name.as_str()),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::TSTypeReference(reference) => {
            let (span, text) = ts_type_name_span_and_text(&reference.type_name)?;
            (span, text, checker.get_type_at_location(node_ref))
        }
        AstKind::Directive(directive) => (
            directive.span,
            Cow::Borrowed(directive.span.source_text(source_text)),
            checker.get_type_at_location(node_ref),
        ),
        AstKind::ExpressionStatement(statement) => {
            let expression_text = statement.span.source_text(source_text);
            if matches!(
                entry.semantic().nodes().parent_kind(node_id),
                AstKind::ArrowFunctionExpression(_)
            ) || matches!(
                entry.semantic().nodes().parent_kind(node_id),
                AstKind::FunctionBody(body) if body.span == statement.span
            ) {
                return None;
            }
            (
                statement.span,
                Cow::Borrowed(expression_text),
                checker.get_type_at_location(node_ref),
            )
        }
        AstKind::TSIndexSignatureName(signature_name) => (
            // TODO(oxc): there is no way to get the span for an index signature name identifier
            // yet, so we'll just construct our own that is approximately correct
            Span::new(
                signature_name.span.start,
                signature_name.type_annotation.span.start,
            ),
            Cow::Borrowed(signature_name.name.as_str()),
            checker.get_type_at_location(node_ref),
        ),
        _ => return None,
    };

    if ty.is_none() {
        return None;
    }

    let ty_variant = ty.enum_variant_name(arena);
    let ast_kind = conformance_ast_type_name(kind.ty());
    let ty_repr = checker.type_to_string(ty, node_ref);

    Some(TypeRecord {
        path: Arc::clone(path),
        start: span.start,
        end: span.end,
        text: sanitize_cow(text),
        ty_variant: Some(ty_variant),
        ast_kind: Some(ast_kind),
        ty_repr: sanitize_owned(ty_repr),
    })
}

fn conformance_ast_type_name(ast_type: AstType) -> &'static str {
    match ast_type {
        AstType::BindingIdentifier => "BindingIdentifier",
        AstType::IdentifierReference => "IdentifierReference",
        AstType::IdentifierName => "IdentifierName",
        AstType::TSPropertySignature => "TSPropertySignature",
        AstType::ObjectProperty => "ObjectProperty",
        AstType::StaticMemberExpression => "StaticMemberExpression",
        AstType::MethodDefinition => "MethodDefinition",
        AstType::TSMethodSignature => "TSMethodSignature",
        AstType::ExportSpecifier => "ExportSpecifier",
        AstType::TSThisParameter => "TSThisParameter",
        AstType::PropertyDefinition => "PropertyDefinition",
        AstType::TSTypeAliasDeclaration => "TSTypeAliasDeclaration",
        AstType::TSImportEqualsDeclaration => "TSImportEqualsDeclaration",
        AstType::TSInterfaceDeclaration => "TSInterfaceDeclaration",
        AstType::TSEnumDeclaration => "TSEnumDeclaration",
        AstType::TSEnumMember => "TSEnumMember",
        AstType::TSModuleDeclaration => "TSModuleDeclaration",
        AstType::TSTypeParameter => "TSTypeParameter",
        AstType::TSMappedType => "TSMappedType",
        AstType::TSClassImplements => "TSClassImplements",
        AstType::TSInterfaceHeritage => "TSInterfaceHeritage",
        AstType::TSTypeReference => "TSTypeReference",
        AstType::Directive => "Directive",
        AstType::ExpressionStatement => "ExpressionStatement",
        AstType::TSIndexSignatureName => "TSIndexSignatureName",
        _ => unreachable!("unsupported conformance AST type: {ast_type:?}"),
    }
}

fn identifier_property_key_span_and_text<'a>(key: &'a PropertyKey<'a>) -> Option<(Span, &'a str)> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => {
            Some((identifier.span, identifier.name.as_str()))
        }
        PropertyKey::Identifier(identifier) => Some((identifier.span, identifier.name.as_str())),
        _ => None,
    }
}

fn ts_module_declaration_name_span_and_text<'a>(
    name: &'a oxc_ast::ast::TSModuleDeclarationName<'a>,
) -> Option<(Span, &'a str)> {
    match name {
        oxc_ast::ast::TSModuleDeclarationName::Identifier(identifier) => {
            Some((identifier.span, &identifier.name))
        }
        oxc_ast::ast::TSModuleDeclarationName::StringLiteral(literal) => {
            Some((literal.span, &literal.value))
        }
    }
}

fn module_export_name_span_and_text<'a>(
    name: &'a oxc_ast::ast::ModuleExportName<'a>,
) -> Option<(Span, &'a str)> {
    match name {
        oxc_ast::ast::ModuleExportName::IdentifierName(identifier) => {
            Some((identifier.span, &identifier.name))
        }
        oxc_ast::ast::ModuleExportName::IdentifierReference(identifier) => {
            Some((identifier.span, &identifier.name))
        }
        oxc_ast::ast::ModuleExportName::StringLiteral(literal) => {
            Some((literal.span, &literal.value))
        }
    }
}

fn ts_type_name_span_and_text<'a>(name: &'a TSTypeName<'a>) -> Option<(Span, Cow<'a, str>)> {
    match name {
        TSTypeName::IdentifierReference(identifier) => {
            Some((identifier.span, Cow::Borrowed(identifier.name.as_str())))
        }
        TSTypeName::QualifiedName(qualified) => Some((
            qualified.right.span,
            Cow::Borrowed(qualified.right.name.as_str()),
        )),
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
                    Some(oxc_type) if type_reprs_are_equivalent(tsc_type, oxc_type) => {
                        matched_types += 1;
                    }
                    Some(oxc_type) => errors.push(ComparisonError::TypeMismatch {
                        start: key.start,
                        text: key.text.clone(),
                        expected: tsc_type.clone(),
                        actual: oxc_type.clone(),
                    }),
                    None => errors.push(ComparisonError::MissingFromOxc {
                        start: key.start,
                        text: key.text.clone(),
                        expected: tsc_type.clone(),
                    }),
                }
            }

            for (key, oxc_type) in oxc_by_key {
                if !tsc_by_key.contains_key(key) {
                    errors.push(ComparisonError::ExtraInOxc {
                        start: key.start,
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

fn type_reprs_are_equivalent(expected: &str, actual: &str) -> bool {
    expected == actual
        || normalize_union_order_for_comparison(expected)
            == normalize_union_order_for_comparison(actual)
}

fn normalize_union_order_for_comparison(type_repr: &str) -> String {
    let nested = normalize_nested_type_contexts(type_repr);
    normalize_top_level_union_chains(&nested)
}

fn normalize_nested_type_contexts(type_repr: &str) -> String {
    let mut normalized = String::new();
    let mut index = 0;

    while index < type_repr.len() {
        let (character, next_index) = char_at(type_repr, index);
        if character == '`' {
            let (template, next_index) = normalize_template_literal_type_part(type_repr, index);
            normalized.push_str(&template);
            index = next_index;
        } else if matches!(character, '\'' | '"') {
            let quoted_end = quoted_type_part_end(type_repr, index);
            normalized.push_str(&type_repr[index..quoted_end]);
            index = quoted_end;
        } else if is_open_type_delimiter(character) {
            if let Some(close_index) = matching_type_delimiter_index(type_repr, index) {
                normalized.push(character);
                normalized.push_str(&normalize_union_order_for_comparison(
                    &type_repr[next_index..close_index],
                ));
                let (close, close_next_index) = char_at(type_repr, close_index);
                normalized.push(close);
                index = close_next_index;
            } else {
                normalized.push(character);
                index = next_index;
            }
        } else {
            normalized.push(character);
            index = next_index;
        }
    }

    normalized
}

fn normalize_template_literal_type_part(type_repr: &str, start: usize) -> (String, usize) {
    let mut normalized = String::from("`");
    let mut index = char_at(type_repr, start).1;

    while index < type_repr.len() {
        let (character, next_index) = char_at(type_repr, index);
        if character == '\\' {
            normalized.push_str(&type_repr[index..next_index]);
            index = next_index;
            if index < type_repr.len() {
                let escaped_end = char_at(type_repr, index).1;
                normalized.push_str(&type_repr[index..escaped_end]);
                index = escaped_end;
            }
        } else if character == '`' {
            normalized.push('`');
            return (normalized, next_index);
        } else if character == '$' && type_repr[next_index..].starts_with('{') {
            let open_brace = next_index;
            let expression_start = char_at(type_repr, open_brace).1;
            normalized.push_str("${");
            let Some(close_brace) = matching_type_delimiter_index(type_repr, open_brace) else {
                normalized.push_str(&type_repr[expression_start..]);
                return (normalized, type_repr.len());
            };
            normalized.push_str(&normalize_union_order_for_comparison(
                &type_repr[expression_start..close_brace],
            ));
            normalized.push('}');
            index = char_at(type_repr, close_brace).1;
        } else {
            normalized.push_str(&type_repr[index..next_index]);
            index = next_index;
        }
    }

    (normalized, type_repr.len())
}

fn normalize_top_level_union_chains(type_repr: &str) -> String {
    let mut normalized = String::new();
    let mut cursor = 0;

    while let Some(pipe_index) = top_level_pipe_index(type_repr, cursor) {
        let start = union_chain_start(type_repr, pipe_index);
        let end = union_chain_end(type_repr, pipe_index);
        if start < cursor {
            cursor = pipe_index + 1;
            continue;
        }

        normalized.push_str(&type_repr[cursor..start]);
        normalized.push_str(&normalize_union_chain(&type_repr[start..end]));
        cursor = end;
    }

    normalized.push_str(&type_repr[cursor..]);
    normalized
}

fn normalize_union_chain(union_chain: &str) -> String {
    let mut types = split_top_level_union_types(union_chain)
        .into_iter()
        .map(|ty| ty.trim().to_string())
        .collect::<Vec<_>>();
    if types.len() < 2 {
        return union_chain.to_string();
    }

    types.sort();
    types.join(" | ")
}

fn split_top_level_union_types(union_chain: &str) -> Vec<&str> {
    let mut types = Vec::new();
    let mut start = 0;
    let mut index = 0;
    let mut closing_delimiters = Vec::new();

    while index < union_chain.len() {
        let (character, next_index) = char_at(union_chain, index);
        if matches!(character, '\'' | '"' | '`') {
            index = quoted_type_part_end(union_chain, index);
            continue;
        }

        if is_open_type_delimiter(character) {
            closing_delimiters.push(close_type_delimiter(character));
        } else if closing_delimiters.last().copied() == Some(character)
            && !is_arrow_greater_than(union_chain, index, character)
        {
            closing_delimiters.pop();
        } else if character == '|' && closing_delimiters.is_empty() {
            types.push(&union_chain[start..index]);
            start = next_index;
        }

        index = next_index;
    }

    types.push(&union_chain[start..]);
    types
}

fn top_level_pipe_index(type_repr: &str, start: usize) -> Option<usize> {
    let mut index = start;
    let mut closing_delimiters = Vec::new();

    while index < type_repr.len() {
        let (character, next_index) = char_at(type_repr, index);
        if matches!(character, '\'' | '"' | '`') {
            index = quoted_type_part_end(type_repr, index);
            continue;
        }

        if is_open_type_delimiter(character) {
            closing_delimiters.push(close_type_delimiter(character));
        } else if closing_delimiters.last().copied() == Some(character)
            && !is_arrow_greater_than(type_repr, index, character)
        {
            closing_delimiters.pop();
        } else if character == '|' && closing_delimiters.is_empty() {
            return Some(index);
        }

        index = next_index;
    }

    None
}

fn union_chain_start(type_repr: &str, pipe_index: usize) -> usize {
    let mut index = 0;
    let mut start = 0;
    let mut closing_delimiters = Vec::new();

    while index < pipe_index {
        let (character, next_index) = char_at(type_repr, index);
        if matches!(character, '\'' | '"' | '`') {
            index = quoted_type_part_end(type_repr, index);
            continue;
        }

        if is_open_type_delimiter(character) {
            closing_delimiters.push(close_type_delimiter(character));
        } else if closing_delimiters.last().copied() == Some(character)
            && !is_arrow_greater_than(type_repr, index, character)
        {
            closing_delimiters.pop();
        } else if closing_delimiters.is_empty() {
            if matches!(character, ',' | ':' | ';') {
                start = next_index;
            } else if character == '=' {
                start = if type_repr[next_index..].starts_with('>') {
                    next_index + 1
                } else {
                    next_index
                };
            } else if type_repr[index..].starts_with(" extends ") {
                start = index + " extends ".len();
            }
        }

        index = next_index;
    }

    skip_whitespace(type_repr, start, pipe_index)
}

fn union_chain_end(type_repr: &str, pipe_index: usize) -> usize {
    let mut index = pipe_index + 1;
    let mut closing_delimiters = Vec::new();

    while index < type_repr.len() {
        let (character, next_index) = char_at(type_repr, index);
        if matches!(character, '\'' | '"' | '`') {
            index = quoted_type_part_end(type_repr, index);
            continue;
        }

        if is_open_type_delimiter(character) {
            closing_delimiters.push(close_type_delimiter(character));
        } else if closing_delimiters.last().copied() == Some(character)
            && !is_arrow_greater_than(type_repr, index, character)
        {
            closing_delimiters.pop();
        } else if closing_delimiters.is_empty()
            && (matches!(character, ',' | ';')
                || (character == '=' && !type_repr[next_index..].starts_with('>')))
        {
            return trim_end_whitespace(type_repr, index, pipe_index + 1);
        }

        index = next_index;
    }

    trim_end_whitespace(type_repr, type_repr.len(), pipe_index + 1)
}

fn skip_whitespace(type_repr: &str, mut index: usize, end: usize) -> usize {
    while index < end {
        let (character, next_index) = char_at(type_repr, index);
        if !character.is_whitespace() {
            break;
        }
        index = next_index;
    }
    index
}

fn trim_end_whitespace(type_repr: &str, mut index: usize, start: usize) -> usize {
    while index > start {
        let Some((previous_index, character)) = type_repr[..index].char_indices().next_back()
        else {
            break;
        };
        if !character.is_whitespace() {
            break;
        }
        index = previous_index;
    }
    index
}

fn matching_type_delimiter_index(type_repr: &str, open_index: usize) -> Option<usize> {
    let (open, mut index) = char_at(type_repr, open_index);
    let mut closing_delimiters = vec![close_type_delimiter(open)];

    while index < type_repr.len() {
        let (character, next_index) = char_at(type_repr, index);
        if matches!(character, '\'' | '"' | '`') {
            index = quoted_type_part_end(type_repr, index);
            continue;
        }

        if is_open_type_delimiter(character) {
            closing_delimiters.push(close_type_delimiter(character));
        } else if closing_delimiters.last().copied() == Some(character)
            && !is_arrow_greater_than(type_repr, index, character)
        {
            closing_delimiters.pop();
            if closing_delimiters.is_empty() {
                return Some(index);
            }
        }

        index = next_index;
    }

    None
}

fn quoted_type_part_end(type_repr: &str, quote_index: usize) -> usize {
    let (quote, mut index) = char_at(type_repr, quote_index);

    while index < type_repr.len() {
        let (character, next_index) = char_at(type_repr, index);
        if character == '\\' {
            index = next_index;
            if index < type_repr.len() {
                index = char_at(type_repr, index).1;
            }
            continue;
        }
        if character == quote {
            return next_index;
        }
        index = next_index;
    }

    type_repr.len()
}

fn char_at(text: &str, index: usize) -> (char, usize) {
    let character = text[index..]
        .chars()
        .next()
        .expect("index must be at a char boundary");
    (character, index + character.len_utf8())
}

fn is_arrow_greater_than(text: &str, index: usize, character: char) -> bool {
    character == '>' && text[..index].ends_with('=')
}

fn is_open_type_delimiter(character: char) -> bool {
    matches!(character, '(' | '[' | '{' | '<')
}

fn close_type_delimiter(character: char) -> char {
    match character {
        '(' => ')',
        '[' => ']',
        '{' => '}',
        '<' => '>',
        _ => unreachable!("expected an opening delimiter"),
    }
}

fn records_by_file(records: &[TypeRecord]) -> BTreeMap<Arc<str>, TypeRecordMap> {
    let mut by_file = BTreeMap::new();
    for record in records {
        by_file
            .entry(record.path.clone())
            .or_insert_with(TypeRecordMap::new)
            .insert(record.key(), record.ty_repr.clone());
    }
    by_file
}

fn read_records(path: &Path) -> ConformanceResult<Vec<TypeRecord>> {
    let text = read_to_string_simd_utf8(path).map_err(|err| {
        ConformanceError::new(format!(
            "failed to read checked-in TypeScript type records {}: {err}\nrun `cargo conformance-refresh` to regenerate them",
            path.display()
        ))
    })?;
    parse_records(&text, &path.display().to_string())
}

fn parse_records(text: &str, source: &str) -> ConformanceResult<Vec<TypeRecord>> {
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            TypeRecord::from_tsv(line).map_err(|err| {
                ConformanceError::new(format!("invalid type record in {source}: {err}: {line}"))
            })
        })
        .collect()
}

fn write_type_outputs(
    suite: &ConformanceSuite,
    cases_root: &Path,
    records: &[TypeRecord],
    expected_records: &[TypeRecord],
) {
    if !suite.write_type_outputs {
        return;
    }

    let mismatches_by_path = type_output_mismatches(expected_records, records);
    let mut records_by_path = BTreeMap::new();
    for record in records {
        records_by_path
            .entry(record.path.as_ref())
            .or_insert_with(Vec::new)
            .push(record);
    }

    for path in discover_compiler_cases(suite, cases_root) {
        let relative_path = relative_path(cases_root, &path);
        let source_text = match read_to_string_simd_utf8(&path) {
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
                mismatches_by_path.get(record_path.as_str()),
            );
        }

        let output_path = type_output_path(suite, cases_root, &path);
        if let Some(parent) = output_path.parent() {
            std::fs::create_dir_all(parent).unwrap_or_else(|err| {
                panic!(
                    "failed to create type output directory {}: {err}",
                    parent.display()
                )
            });
        }
        std::fs::write(&output_path, output).unwrap_or_else(|err| {
            panic!(
                "failed to write type output {}: {err}",
                output_path.display()
            )
        });
    }
}

fn type_output_mismatches(
    expected_records: &[TypeRecord],
    records: &[TypeRecord],
) -> BTreeMap<Arc<str>, TypeRecordMap> {
    let expected_by_file = records_by_file(expected_records);
    let records_by_file = records_by_file(records);
    let mut mismatches = BTreeMap::new();

    for (path, expected_by_key) in expected_by_file {
        let Some(records_by_key) = records_by_file.get(&path) else {
            continue;
        };

        for (key, expected_type) in expected_by_key {
            if let Some(actual_type) = records_by_key.get(&key)
                && !type_reprs_are_equivalent(&expected_type, actual_type)
            {
                mismatches
                    .entry(path.clone())
                    .or_insert_with(TypeRecordMap::new)
                    .insert(key, expected_type);
            }
        }
    }

    mismatches
}

fn type_output_path(suite: &ConformanceSuite, cases_root: &Path, path: &Path) -> PathBuf {
    let Some(type_outputs_root) = suite.type_outputs_root else {
        return sibling_type_output_path(path);
    };

    let relative_path = path.strip_prefix(cases_root).unwrap_or(path);
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join(type_outputs_root)
        .join(sibling_type_output_path(relative_path))
}

fn sibling_type_output_path(path: &Path) -> PathBuf {
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
    mismatches: Option<&TypeRecordMap>,
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
        output.push_str(": ");
        output.push_str(&record.ty_repr);
        if let Some(ty_variant) = record.ty_variant {
            output.push_str("   (");
            output.push_str(ty_variant);
            output.push(')');
        }
        if let Some(ast_kind) = &record.ast_kind {
            output.push_str(" (");
            output.push_str(ast_kind);
            output.push(')');
        }
        output.push('\n');

        if let Some(expected_type) = mismatches.and_then(|mismatches| mismatches.get(&record.key()))
        {
            let colon_column = 1 + marker_column + caret_count;
            output.extend(std::iter::repeat_n(
                ' ',
                colon_column.saturating_sub("expected".len()),
            ));
            output.push_str("expected: ");
            output.push_str(expected_type);
            output.push('\n');
        }
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
    let mut sanitized = String::with_capacity(value.len());
    let mut previous_was_control_whitespace = false;
    for character in value.chars() {
        if matches!(character, '\t' | '\r' | '\n') {
            if !previous_was_control_whitespace {
                sanitized.push(' ');
            }
            previous_was_control_whitespace = true;
        } else {
            sanitized.push(character);
            previous_was_control_whitespace = false;
        }
    }
    sanitized.trim().to_string()
}

fn sanitize_cow(value: Cow<'_, str>) -> String {
    if !needs_sanitization(&value) {
        return value.into_owned();
    }
    sanitize(&value)
}

fn sanitize_owned(value: String) -> String {
    if !needs_sanitization(&value) {
        return value;
    }
    sanitize(&value)
}

fn needs_sanitization(value: &str) -> bool {
    value.trim().len() != value.len()
        || value
            .bytes()
            .any(|byte| matches!(byte, b'\t' | b'\r' | b'\n'))
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
    let snapshot = format_type_record_report(suite, stats, results);

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

fn format_type_record_report(
    suite: &ConformanceSuite,
    stats: &ComparisonStats,
    results: &[FileResult],
) -> String {
    let mut snapshot = String::new();
    snapshot.push_str(&format!(
        "# {} type-record conformance snapshot\n",
        suite.name
    ));
    snapshot.push_str("# Generated by `cargo conformance`.\n");
    snapshot.push_str(&format!("# Cases root: {}\n", suite.cases_root));
    snapshot.push_str(&format!(
        "files: passed={} failed={} panicked={} total={} pass_percentage={:.2}%\n",
        stats.passed_files,
        stats.failed_files,
        stats.panicked_files,
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

    snapshot
}

fn filter_panicked_records(
    records: Vec<TypeRecord>,
    panicked_paths: &BTreeSet<String>,
) -> Vec<TypeRecord> {
    records
        .into_iter()
        .filter(|record| !panicked_paths.contains(record.path.as_ref()))
        .collect()
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
    let Ok(source_text) = read_to_string_simd_utf8(&source_path) else {
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
    fn prepared_batch_count_amortizes_catalogs_and_caps_at_workers() {
        assert_eq!(conformance_batch_count(0, 8), 0);
        assert_eq!(conformance_batch_count(1, 8), 1);
        assert_eq!(conformance_batch_count(9, 8), 3);
        assert_eq!(conformance_batch_count(55, 8), 8);
    }

    #[test]
    fn conformance_batches_are_balanced_by_source_size() {
        let files = [10, 9, 8, 7]
            .into_iter()
            .enumerate()
            .map(|(index, size)| ReadyConformanceFile {
                path: PathBuf::from(format!("{index}.ts")),
                source_text: "x".repeat(size),
            })
            .collect();

        let batches = balance_conformance_batches(files, 2);
        let sizes = batches
            .iter()
            .map(|batch| {
                batch
                    .files
                    .iter()
                    .map(|file| file.source_text.len())
                    .sum::<usize>()
            })
            .collect::<Vec<_>>();

        assert_eq!(sizes, vec![17, 17]);
    }

    fn target_from_args(args: &[&str]) -> ConformanceResult<ConformanceTarget> {
        conformance_target_from_arguments(
            Path::new(env!("CARGO_MANIFEST_DIR")),
            args.iter().map(std::ffi::OsString::from),
        )
    }

    fn suite_names(target: &ConformanceTarget) -> Vec<&'static str> {
        target.suites.iter().map(|suite| suite.name).collect()
    }

    #[test]
    fn conformance_target_full_selects_all_suites() {
        let target = target_from_args(&["full"]).unwrap();

        assert_eq!(
            suite_names(&target),
            suite_names(&ConformanceTarget {
                case_path: None,
                suites: all_conformance_suites().to_vec(),
                refresh_tsc: false,
            })
        );
    }

    #[test]
    fn conformance_target_ignores_test_harness_arguments() {
        let target = target_from_args(&[
            "conformance::full_conformance",
            "--exact",
            "--nocapture",
            "typescript",
        ])
        .unwrap();

        assert_eq!(suite_names(&target), vec![TYPESCRIPT_SUITE.name]);
    }

    #[test]
    fn conformance_target_rejects_unknown_arguments() {
        let error = match target_from_args(&["typecript"]) {
            Ok(_) => panic!("expected unknown argument error"),
            Err(error) => error,
        };

        assert_eq!(
            error.into_message(),
            "unknown conformance target argument: typecript"
        );
    }

    #[test]
    fn collection_progress_fits_active_files_on_one_line() {
        let state = ConformanceCollectionProgressState {
            completed_paths: 4,
            active_paths: [
                PathBuf::from("alpha.ts"),
                PathBuf::from("beta.ts"),
                PathBuf::from("gamma.ts"),
                PathBuf::from("delta.ts"),
            ]
            .into_iter()
            .collect(),
        };

        let line = format_collection_progress(&state, 53, 40);

        assert!(line.len() <= 40, "{line:?}");
        assert_eq!(line, "collecting 4/53 [alpha.ts, beta.ts, +2]");
    }

    #[test]
    fn collection_progress_truncates_a_long_active_file() {
        let state = ConformanceCollectionProgressState {
            completed_paths: 0,
            active_paths: [PathBuf::from(
                "conditionalTypeDiscriminatingLargeUnionRegularTypeFetchingSpeedReasonable.ts",
            )]
            .into_iter()
            .collect(),
        };

        let line = format_collection_progress(&state, 1, 40);

        assert!(line.len() <= 40, "{line:?}");
        assert_eq!(line, "collecting 0/1 [conditionalTypeDiscr...]");
    }

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
    fn compiler_test_case_parser_collects_bom_prefixed_directive() {
        let parsed = parse_compiler_test_case(
            "\u{feff}// @target: es2015\nnamespace EmptyTypes {\n    interface iface { }\n}",
            "compiler/arrayBestCommonTypes.ts",
        );

        assert_eq!(parsed.settings.get("target").unwrap(), "es2015");
        assert_eq!(parsed.files.len(), 1);
        assert_eq!(
            parsed.files[0].source_text,
            "namespace EmptyTypes {\n    interface iface { }\n}"
        );
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
    fn explicit_virtual_files_parse_as_modules_without_mutating_fixture_text() {
        let parsed = parse_compiler_test_case(
            "// @filename: a.ts\nconst createValue = () => 'value';\n// @filename: b.ts\nconst createValue = async () => 'value';",
            "compiler/eslint_awaitThenable.ts",
        );
        let allocator = Allocator::default();
        let fixture = parse_fixture_program(&allocator, &parsed, None).unwrap();
        let b_path = normalize_fixture_path(Path::new("b.ts"));
        let b_entry = fixture
            .store
            .id_for_path(&b_path)
            .and_then(|program_id| fixture.store.entry(program_id))
            .unwrap();

        assert_eq!(
            parsed.files[1].source_text,
            "const createValue = async () => 'value';"
        );
        assert!(b_entry.source_text().ends_with(VIRTUAL_MODULE_MARKER));
    }

    #[test]
    fn explicit_virtual_module_files_do_not_merge_same_named_functions() {
        let source_text = "// @filename: a.ts\nfunction value() { return 1; }\n// @filename: b.ts\nfunction value() { return 2; }";

        let records = collect_oxc_records_from_source(
            Path::new("tests/conformance/cases"),
            Path::new("tests/conformance/cases/compiler/virtualModules.ts"),
            source_text,
        );

        assert!(records.iter().any(|record| {
            record.path.as_ref() == "compiler/virtualModules.ts::a.ts"
                && record.text == "value"
                && record.ty_repr == "() => number"
        }));
        assert!(records.iter().any(|record| {
            record.path.as_ref() == "compiler/virtualModules.ts::b.ts"
                && record.text == "value"
                && record.ty_repr == "() => number"
        }));
        assert!(!records.iter().any(|record| {
            record.text == "value" && record.ty_repr == "{ (): number; (): number; }"
        }));
    }

    #[test]
    fn explicit_virtual_module_files_do_not_merge_same_named_interfaces() {
        let source_text = "// @filename: a.ts\ninterface MyThenable { then(onFulfilled: () => void): MyThenable; }\n// @filename: b.ts\ninterface MyThenable { then(onFulfilled: () => void): MyThenable; }";

        let records = collect_oxc_records_from_source(
            Path::new("tests/conformance/cases"),
            Path::new("tests/conformance/cases/compiler/virtualModules.ts"),
            source_text,
        );

        for path in [
            "compiler/virtualModules.ts::a.ts",
            "compiler/virtualModules.ts::b.ts",
        ] {
            assert!(records.iter().any(|record| {
                record.path.as_ref() == path
                    && record.text == "then"
                    && record.ty_repr == "(onFulfilled: () => void) => MyThenable"
            }));
        }
        assert!(!records.iter().any(|record| {
            record.text == "then"
                && record.ty_repr
                    == "{ (onFulfilled: () => void): MyThenable; (onFulfilled: () => void): MyThenable; }"
        }));
    }

    #[test]
    fn type_alias_name_emits_one_type_meaning_record_for_merged_symbol() {
        let source_text = "type NodeFilter = ((value: string) => number) | { accept(value: string): number };\ndeclare var NodeFilter: { readonly VALUE: 1 };";
        let alias_start = u32::try_from(source_text.find("NodeFilter").unwrap()).unwrap();
        let alias_end = alias_start + u32::try_from("NodeFilter".len()).unwrap();

        let records = collect_oxc_records_from_source(
            Path::new("tests/conformance/cases"),
            Path::new("tests/conformance/cases/compiler/mergedTypeValueSymbol.ts"),
            source_text,
        );
        let alias_records = records
            .iter()
            .filter(|record| record.start == alias_start && record.end == alias_end)
            .collect::<Vec<_>>();

        assert_eq!(alias_records.len(), 1);
        assert_eq!(
            alias_records[0].ty_repr,
            "((value: string) => number) | { accept(value: string): number; }"
        );
        assert_eq!(alias_records[0].ast_kind, Some("TSTypeAliasDeclaration"));
    }

    #[test]
    fn type_output_renders_line_span_and_type() {
        let source_text = "let count: number = 1;\nlet label: string = \"ready\";";
        let record = TypeRecord {
            path: Arc::from("compiler/basicPrimitives.ts"),
            start: 27,
            end: 32,
            text: "label".to_string(),
            ty_variant: Some("TyString"),
            ast_kind: Some("IdentifierReference"),
            ty_repr: "string".to_string(),
        };
        let mut output = String::new();

        write_type_output_for_source_file(&mut output, source_text, &[&record], None);

        assert_eq!(
            output,
            "let label: string = \"ready\";\n>   ^^^^^: string   (TyString) (IdentifierReference)\n"
        );
    }

    #[test]
    fn type_output_renders_mismatch_expected_type_on_separate_line() {
        let source_text = "let count: number = 1;";
        let record = TypeRecord {
            path: Arc::from("compiler/basicPrimitives.ts"),
            start: 4,
            end: 9,
            text: "count".to_string(),
            ty_variant: Some("TyString"),
            ast_kind: Some("IdentifierReference"),
            ty_repr: "string".to_string(),
        };
        let mut mismatches = TypeRecordMap::new();
        mismatches.insert(record.key(), "number".to_string());
        let mut output = String::new();

        write_type_output_for_source_file(&mut output, source_text, &[&record], Some(&mismatches));

        assert_eq!(
            output,
            "let count: number = 1;\n>   ^^^^^: string   (TyString) (IdentifierReference)\n expected: number\n"
        );
    }

    #[test]
    fn type_output_path_appends_types_extension() {
        assert_eq!(
            sibling_type_output_path(Path::new("tests/conformance/cases/compiler/example.ts")),
            PathBuf::from("tests/conformance/cases/compiler/example.ts.types")
        );
    }

    #[test]
    fn type_output_path_can_write_under_suite_output_root() {
        assert_eq!(
            type_output_path(
                &STANDARD_LIBRARY_SUITE,
                Path::new("/repo/src/lib"),
                Path::new("/repo/src/lib/es5.d.ts"),
            ),
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/conformance/lib/es5.d.ts.types")
        );
    }

    #[test]
    fn type_repr_equivalence_ignores_union_order() {
        assert!(type_reprs_are_equivalent("A | B", "B | A"));
        assert!(type_reprs_are_equivalent(
            "<T, U = B | T>(value: A | B) => [B | A, C]",
            "<T, U = T | B>(value: B | A) => [A | B, C]",
        ));
        assert!(type_reprs_are_equivalent(
            "Box<() => A | B>",
            "Box<() => B | A>",
        ));
        assert!(type_reprs_are_equivalent(
            r"`${K}.${PathInternal<V, V | TraversedTypes>}`",
            r"`${K}.${PathInternal<V, TraversedTypes | V>}`",
        ));
        assert!(!type_reprs_are_equivalent("A | B", "A | C"));
    }

    #[test]
    fn compare_records_counts_union_order_only_differences_as_matches() {
        let expected = TypeRecord {
            path: Arc::from("compiler/unionOrder.ts"),
            start: 0,
            end: 5,
            text: "value".to_string(),
            ty_variant: None,
            ast_kind: None,
            ty_repr: "<T, U = B | T>(value: A | B) => B | A".to_string(),
        };
        let actual = TypeRecord {
            ty_repr: "<T, U = T | B>(value: B | A) => A | B".to_string(),
            ..expected.clone()
        };

        let results = compare_records(&[expected], &[actual]);

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].matched_types, 1);
        assert!(results[0].errors.is_empty());
    }

    #[test]
    fn ambient_namespace_with_statement_emits_namespace_and_export_records() {
        let source_text = "// @target: es2015\ndeclare namespace M1 {\n    while(true);\n\n    export var v1 = () => false;\n}";
        let records = collect_oxc_records_from_source(
            Path::new("vendor/TypeScript/tests/cases"),
            Path::new("vendor/TypeScript/tests/cases/compiler/ambientStatement1.ts"),
            source_text,
        );

        assert!(records.iter().any(|record| {
            record.path.as_ref() == "compiler/ambientStatement1.ts"
                && record.text == "M1"
                && record.ty_repr == "typeof M1"
        }));
        assert!(records.iter().any(|record| {
            record.path.as_ref() == "compiler/ambientStatement1.ts"
                && record.text == "v1"
                && record.ty_repr == "() => boolean"
        }));
    }

    #[test]
    fn expression_statement_records_use_whole_statement_text() {
        let source_text = "declare function x(): number;\nx();";
        let records = collect_oxc_records_from_source(
            Path::new("tests/conformance/cases"),
            Path::new("tests/conformance/cases/compiler/expressionStatement.ts"),
            source_text,
        );

        assert!(records.iter().any(|record| {
            record.path.as_ref() == "compiler/expressionStatement.ts"
                && record.text == "x();"
                && record.ty_repr == "number"
        }));
    }

    #[test]
    fn panicked_fixture_is_excluded_from_record_comparison() {
        let source_text = "// @target: es2015\n// @strict: false\nclass C {\n    public const var export foo = 10;\n\n    var constructor() { }\n}";
        let allocator = Allocator::default();
        let collection = collect_oxc_records_from_source_with_programs(
            Path::new("vendor/TypeScript/tests/cases"),
            Path::new("vendor/TypeScript/tests/cases/compiler/ClassDeclaration26.ts"),
            source_text,
            &allocator,
            None,
        );

        assert!(collection.records.is_empty());
        assert_eq!(
            collection.panicked_paths,
            BTreeSet::from(["compiler/ClassDeclaration26.ts".to_string()])
        );

        let stats = ComparisonStats::from_results(&[], collection.panicked_paths.len());
        assert_eq!(stats.mismatched_types, 0);
        assert_eq!(stats.total_types, 0);
        assert_eq!(stats.panicked_files, 1);
    }

    #[test]
    fn sanitize_collapses_consecutive_control_whitespace() {
        assert_eq!(
            sanitize("first\n\nsecond\r\nthird\t\tfourth"),
            "first second third fourth"
        );

        let clean = String::from("already clean");
        let allocation = clean.as_ptr();
        let sanitized = sanitize_owned(clean);
        assert_eq!(sanitized, "already clean");
        assert_eq!(sanitized.as_ptr(), allocation);
    }
}
