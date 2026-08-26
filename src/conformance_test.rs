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
            && record.r#type.display == "() => number"
    }));
    assert!(records.iter().any(|record| {
        record.path.as_ref() == "compiler/virtualModules.ts::b.ts"
            && record.text == "value"
            && record.r#type.display == "() => number"
    }));
    assert!(!records.iter().any(|record| {
        record.text == "value" && record.r#type.display == "{ (): number; (): number; }"
    }));
}

#[test]
fn renamed_object_binding_keys_use_the_bound_property_type() {
    let source_text = "abstract class Base { abstract value: string; constructor() { const { value: renamed } = this; } }";
    let key_start = u32::try_from(source_text.find("value: renamed").unwrap()).unwrap();
    let records = collect_oxc_records_from_source(
        Path::new("tests/conformance/cases"),
        Path::new("tests/conformance/cases/compiler/renamedBinding.ts"),
        source_text,
    );
    let key_records = records
        .iter()
        .filter(|record| record.start == key_start && record.text == "value")
        .collect::<Vec<_>>();

    assert_eq!(key_records.len(), 1);
    assert_eq!(key_records[0].r#type.display, "string");
}

#[test]
fn renamed_object_assignment_keys_use_the_target_type() {
    let source_text =
        "let source: { value: string }; let renamed: string; ({ value: renamed } = source);";
    let key_start = u32::try_from(source_text.find("value: renamed").unwrap()).unwrap();
    let records = collect_oxc_records_from_source(
        Path::new("tests/conformance/cases"),
        Path::new("tests/conformance/cases/compiler/renamedAssignment.ts"),
        source_text,
    );
    let key_records = records
        .iter()
        .filter(|record| record.start == key_start && record.text == "value")
        .collect::<Vec<_>>();

    assert_eq!(key_records.len(), 1);
    assert_eq!(key_records[0].r#type.display, "string");
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
                && record.r#type.display == "(onFulfilled: () => void) => MyThenable"
        }));
    }
    assert!(!records.iter().any(|record| {
        record.text == "then"
            && record.r#type.display
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
        alias_records[0].r#type.display,
        "((value: string) => number) | { accept(value: string): number; }"
    );
    assert_eq!(alias_records[0].node_type, "Identifier");
}

#[test]
fn type_output_renders_line_span_and_type() {
    let source_text = "let count: number = 1;\nlet label: string = \"ready\";";
    let record = TypeRecord {
        path: Arc::from("compiler/basicPrimitives.ts"),
        start: 27,
        end: 32,
        text: "label".to_string(),
        node_type: "Identifier".to_string(),
        r#type: TypeRecordType {
            name: "String".to_string(),
            display: "string".to_string(),
        },
        assignability: Vec::new(),
    };
    let mut output = String::new();

    write_type_output_for_source_file(&mut output, source_text, &[&record], None);

    assert_eq!(
        output,
        "let label: string = \"ready\";\n>   ^^^^^: string   (String) (Identifier)\n"
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
        node_type: "Identifier".to_string(),
        r#type: TypeRecordType {
            name: "String".to_string(),
            display: "string".to_string(),
        },
        assignability: Vec::new(),
    };
    let mut mismatches = TypeRecordMap::new();
    mismatches.insert(
        record.key(),
        TypeRecordType {
            name: "Number".to_string(),
            display: "number".to_string(),
        },
    );
    let mut output = String::new();

    write_type_output_for_source_file(&mut output, source_text, &[&record], Some(&mismatches));

    assert_eq!(
        output,
        "let count: number = 1;\n>   ^^^^^: string   (String) (Identifier)\n expected: number\n"
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
fn type_record_json_shape_is_strict_and_round_trips() {
    let json = r#"{"path":"compiler/example.ts","start":4,"end":9,"text":"value","nodeType":"Identifier","type":{"name":"StringLiteral","display":"\"foo\""},"assignability":[{"target":{"start":10,"end":16,"text":"target"},"assignable":true}]}"#;
    let record = parse_records(json, "test record").unwrap().remove(0);

    assert_eq!(record.node_type, "Identifier");
    assert_eq!(record.r#type.name, "StringLiteral");
    assert_eq!(serde_json::to_string(&record).unwrap(), json);
    assert!(
        parse_records(
            &json.replace("\"display\":", "\"extra\":true,\"display\":"),
            "test record"
        )
        .is_err()
    );
    assert!(
        parse_records(
            &json.replace(",\"display\":\"\\\"foo\\\"\"", ""),
            "test record"
        )
        .is_err()
    );
}

#[test]
fn literal_type_is_compatible_with_expected_primitive() {
    let expected = TypeRecordType {
        name: "String".to_string(),
        display: "string".to_string(),
    };
    let actual = TypeRecordType {
        name: "StringLiteral".to_string(),
        display: r#""foo""#.to_string(),
    };

    assert!(type_records_are_compatible(&expected, &actual));
    assert!(!type_records_are_compatible(&actual, &expected));
}

#[test]
fn assignability_uses_expected_primitive_instead_of_oxc_literal() {
    let allocator = Allocator::default();
    let arena = CheckerArena::new(&allocator);
    let literal = TypeBuilder::new(arena).string_literal("arg = true");
    let captured = CapturedTypeRecord {
        record: TypeRecord {
            path: Arc::from("compiler/example.ts::d.ts"),
            start: 24,
            end: 28,
            text: "msg1".to_string(),
            node_type: "Identifier".to_string(),
            r#type: TypeRecordType {
                name: "StringLiteral".to_string(),
                display: r#""arg = true""#.to_string(),
            },
            assignability: Vec::new(),
        },
        ty: literal,
    };
    let expected_types = TypeRecordMap::from([(
        captured.record.key(),
        TypeRecordType {
            name: "String".to_string(),
            display: "string".to_string(),
        },
    )]);

    assert_ne!(literal, Ty::string());
    assert_eq!(
        assignability_type(&captured, Some(&expected_types)),
        Ty::string()
    );
}

#[test]
fn compare_records_counts_union_order_only_differences_as_matches() {
    let expected = TypeRecord {
        path: Arc::from("compiler/unionOrder.ts"),
        start: 0,
        end: 5,
        text: "value".to_string(),
        node_type: "Identifier".to_string(),
        r#type: TypeRecordType {
            name: "Object".to_string(),
            display: "<T, U = B | T>(value: A | B) => B | A".to_string(),
        },
        assignability: Vec::new(),
    };
    let actual = TypeRecord {
        r#type: TypeRecordType {
            name: "Object".to_string(),
            display: "<T, U = T | B>(value: B | A) => A | B".to_string(),
        },
        ..expected.clone()
    };

    let results = compare_records(&[expected], &[actual]);

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].matched_types, 1);
    assert!(results[0].errors.is_empty());
}

#[test]
fn assignability_pairs_are_exhaustive_through_one_hundred_types() {
    assert_eq!(assignability_pairs(0), Vec::new());
    assert_eq!(assignability_pairs(2), vec![(0, 0), (0, 1), (1, 0), (1, 1)]);
    assert_eq!(assignability_pairs(100).len(), 10_000);
}

#[test]
fn assignability_pairs_sample_large_files_directionally() {
    let pairs = assignability_pairs(101);

    assert_eq!(pairs.len(), 404);
    assert_eq!(&pairs[..4], &[(0, 0), (0, 1), (0, 50), (0, 100)]);
    assert!(pairs.contains(&(1, 0)));
}

#[test]
fn assignment_mismatches_have_separate_totals_and_no_file_summary() {
    let target = TypeRecordKey {
        start: 10,
        end: 16,
        text: "target".to_string(),
    };
    let expected = TypeRecord {
        path: Arc::from("compiler/basicPrimitives.ts"),
        start: 0,
        end: 6,
        text: "source".to_string(),
        node_type: "Identifier".to_string(),
        r#type: TypeRecordType {
            name: "NumberLiteral".to_string(),
            display: "1".to_string(),
        },
        assignability: vec![AssignabilityRecord {
            target: target.clone(),
            assignable: true,
        }],
    };
    let expected_target = TypeRecord {
        path: Arc::clone(&expected.path),
        start: target.start,
        end: target.end,
        text: target.text.clone(),
        node_type: "Identifier".to_string(),
        r#type: TypeRecordType {
            name: "Number".to_string(),
            display: "number".to_string(),
        },
        assignability: Vec::new(),
    };
    let actual = TypeRecord {
        assignability: vec![AssignabilityRecord {
            target,
            assignable: false,
        }],
        ..expected.clone()
    };
    let actual_target = TypeRecord {
        r#type: TypeRecordType {
            name: "NumberLiteral".to_string(),
            display: "1".to_string(),
        },
        ..expected_target.clone()
    };
    let results = compare_records(&[expected, expected_target], &[actual, actual_target]);
    let stats = ComparisonStats::from_results(&results, 0);
    let report = format_type_record_report(&CASES_SUITE, &stats, &results);

    assert_eq!(stats.matched_types, 2);
    assert_eq!(stats.mismatched_types, 0);
    assert_eq!(stats.matched_assignments, 0);
    assert_eq!(stats.mismatched_assignments, 1);
    assert!(report.contains("assign: matched=0 mismatched=1 total=1"));
    assert!(report.contains(":1 `source` should be assignable to :1 `target`"));
    assert!(report.contains("      source: 1    (NumberLiteral)\n"));
    assert!(report.contains("      target: number    (Number)\n"));
    assert!(!report.contains("typescript source:"));
    assert!(!report.contains("      expected: true\n      actual:   false\n"));
    let file_header = report
        .lines()
        .find(|line| line.starts_with("FAIL "))
        .unwrap();
    assert!(!file_header.contains("matched_assignments"));
}

#[test]
fn assignment_locations_use_virtual_file_names() {
    assert_eq!(
        assignability_snapshot_location(&CASES_SUITE, "compiler/example.ts::c.ts", &mut None, 0,),
        "c.ts:1"
    );
}

#[test]
fn assignment_mismatches_keep_distinct_typescript_and_oxc_pairs() {
    let mut snapshot = String::new();
    write_snapshot_error(
        &mut snapshot,
        &CASES_SUITE,
        "compiler/example.ts::d.ts",
        &mut None,
        &ComparisonError::AssignabilityMismatch {
            start: 10,
            text: "source".to_string(),
            target_start: 20,
            target_text: "target".to_string(),
            should_be_assignable: true,
            tsc_source_type: TypeRecordType {
                name: "String".to_string(),
                display: "string".to_string(),
            },
            tsc_target_type: TypeRecordType {
                name: "String".to_string(),
                display: "string".to_string(),
            },
            oxc_source_type: TypeRecordType {
                name: "String".to_string(),
                display: "string".to_string(),
            },
            oxc_target_type: TypeRecordType {
                name: "StringLiteral".to_string(),
                display: r#""literal""#.to_string(),
            },
        },
    );

    assert!(snapshot.contains("      typescript source: string    (String)\n"));
    assert!(snapshot.contains("      typescript target: string    (String)\n"));
    assert!(snapshot.contains("      oxc source: string    (String)\n"));
    assert!(snapshot.contains("      oxc target: \"literal\"    (StringLiteral)\n"));
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
            && record.r#type.display == "typeof M1"
    }));
    assert!(records.iter().any(|record| {
        record.path.as_ref() == "compiler/ambientStatement1.ts"
            && record.text == "v1"
            && record.r#type.display == "() => boolean"
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
            && record.r#type.display == "number"
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
