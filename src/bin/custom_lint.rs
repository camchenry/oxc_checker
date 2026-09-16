use std::{
    env,
    error::Error,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process,
};

use proc_macro2::Span;
use syn::{
    Expr, ExprMethodCall, Macro, Pat, Path as SynPath, Token,
    parse::{Parse, ParseStream},
    visit::{self, Visit},
};

struct TyKindHelperRule {
    accessor: &'static str,
    enum_name: &'static str,
    variant: &'static str,
    helper: &'static str,
}

// Add mappings here when a type-kind variant gains a dedicated query helper.
const TY_KIND_HELPER_RULES: &[TyKindHelperRule] = &[
    // Replace `matches!(..., TyKind::Any)` with `.is_any()`
    TyKindHelperRule {
        accessor: "ty_kind",
        enum_name: "TyKind",
        variant: "Any",
        helper: "is_any",
    },
];

struct MatchesInput {
    expression: Expr,
    pattern: Pat,
    guard: Option<Expr>,
}

impl Parse for MatchesInput {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let expression = input.parse()?;
        input.parse::<Token![,]>()?;
        let pattern = Pat::parse_multi(input)?;
        let guard = if input.peek(Token![if]) {
            input.parse::<Token![if]>()?;
            Some(input.parse::<Expr>()?)
        } else {
            None
        };
        input.parse::<Option<Token![,]>>()?;
        Ok(Self {
            expression,
            pattern,
            guard,
        })
    }
}

struct Diagnostic {
    span: Span,
    message: String,
}

struct CustomLinter<'a> {
    ty_kind_helper_rules: &'a [TyKindHelperRule],
    diagnostics: Vec<Diagnostic>,
}

impl<'a> CustomLinter<'a> {
    fn new(ty_kind_helper_rules: &'a [TyKindHelperRule]) -> Self {
        Self {
            ty_kind_helper_rules,
            diagnostics: Vec::new(),
        }
    }

    fn check_ty_kind_helper_matches(&mut self, matches: &MatchesInput, span: Span) {
        if matches.guard.is_some() {
            return;
        }
        let Expr::MethodCall(method_call) = &matches.expression else {
            return;
        };
        let Some(pattern_path) = pattern_path(&matches.pattern) else {
            return;
        };

        for rule in self.ty_kind_helper_rules {
            if method_call_matches(method_call, rule) && path_matches(pattern_path, rule) {
                self.diagnostics.push(Diagnostic {
                    span,
                    message: format!(
                        "use `.{}()` instead of matching on the type kind",
                        rule.helper
                    ),
                });
            }
        }
    }
}

impl<'ast> Visit<'ast> for CustomLinter<'_> {
    fn visit_macro(&mut self, node: &'ast Macro) {
        if node.path.is_ident("matches")
            && let Ok(matches) = syn::parse2::<MatchesInput>(node.tokens.clone())
        {
            self.check_ty_kind_helper_matches(&matches, node.path.segments[0].ident.span());
        }
        visit::visit_macro(self, node);
    }
}

fn pattern_path(pattern: &Pat) -> Option<&SynPath> {
    match pattern {
        Pat::Path(pattern) => Some(&pattern.path),
        _ => None,
    }
}

fn method_call_matches(method_call: &ExprMethodCall, rule: &TyKindHelperRule) -> bool {
    method_call.method == rule.accessor && method_call.args.len() == 1
}

fn path_matches(path: &SynPath, rule: &TyKindHelperRule) -> bool {
    let mut segments = path.segments.iter().rev();
    segments
        .next()
        .is_some_and(|segment| segment.ident == rule.variant)
        && segments
            .next()
            .is_some_and(|segment| segment.ident == rule.enum_name)
}

fn collect_rust_files(path: &Path, files: &mut Vec<PathBuf>) -> Result<(), Box<dyn Error>> {
    if path.is_file() {
        if path.extension() == Some(OsStr::new("rs")) {
            files.push(path.to_owned());
        }
        return Ok(());
    }

    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir()
            && matches!(
                path.file_name().and_then(OsStr::to_str),
                Some(".git" | "target" | "vendor")
            )
        {
            continue;
        }
        collect_rust_files(&path, files)?;
    }
    Ok(())
}

fn lint_file(path: &Path) -> Result<Vec<Diagnostic>, Box<dyn Error>> {
    let source = fs::read_to_string(path)?;
    let syntax = syn::parse_file(&source)?;
    let mut linter = CustomLinter::new(TY_KIND_HELPER_RULES);
    linter.visit_file(&syntax);
    Ok(linter.diagnostics)
}

fn run(paths: impl IntoIterator<Item = PathBuf>) -> Result<bool, Box<dyn Error>> {
    let mut files = Vec::new();
    for path in paths {
        collect_rust_files(&path, &mut files)?;
    }
    files.sort_unstable();

    let mut found = false;
    for file in files {
        for diagnostic in lint_file(&file)? {
            found = true;
            let start = diagnostic.span.start();
            eprintln!(
                "{}:{}:{}: {}",
                file.display(),
                start.line,
                start.column + 1,
                diagnostic.message,
            );
        }
    }
    Ok(found)
}

fn main() -> Result<(), Box<dyn Error>> {
    let paths = env::args_os()
        .skip(1)
        .map(PathBuf::from)
        .collect::<Vec<_>>();
    let paths = if paths.is_empty() {
        vec![PathBuf::from(".")]
    } else {
        paths
    };

    if run(paths)? {
        process::exit(1);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lint(source: &str) -> syn::Result<usize> {
        let syntax = syn::parse_file(source)?;
        let mut linter = CustomLinter::new(TY_KIND_HELPER_RULES);
        linter.visit_file(&syntax);
        Ok(linter.diagnostics.len())
    }

    #[test]
    fn finds_configured_matches() -> syn::Result<()> {
        assert_eq!(
            lint("fn f() { !matches!(self.ty_kind(constraint), TyKind::Any); }")?,
            1
        );
        assert_eq!(
            lint("fn f() { matches!(arena.ty_kind(ty), crate::types::TyKind::Any); }")?,
            1
        );
        assert_eq!(
            lint("fn f() { matches!(self.ty_kind(ty), TyKind::Unknown); }")?,
            1
        );
        Ok(())
    }

    #[test]
    fn ignores_other_shapes() -> syn::Result<()> {
        assert_eq!(lint("fn f() { matches!(ty, TyKind::Any); }")?, 0);
        assert_eq!(
            lint("fn f() { matches!(self.ty_kind(ty), TyKind::Any | TyKind::Unknown); }")?,
            0
        );
        assert_eq!(
            lint("fn f() { matches!(self.ty_kind(ty), TyKind::Any if condition); }")?,
            0
        );
        Ok(())
    }

    #[test]
    fn accepts_additional_rules() -> syn::Result<()> {
        let rules = [TyKindHelperRule {
            accessor: "ty_kind",
            enum_name: "TyKind",
            variant: "Unknown",
            helper: "is_unknown",
        }];
        let syntax =
            syn::parse_file("fn f() { matches!(self.ty_kind(constraint), TyKind::Unknown); }")?;
        let mut linter = CustomLinter::new(&rules);
        linter.visit_file(&syntax);
        assert_eq!(linter.diagnostics.len(), 1);
        assert_eq!(
            linter.diagnostics[0].message,
            "use `.is_unknown()` instead of matching on the type kind"
        );
        Ok(())
    }
}
