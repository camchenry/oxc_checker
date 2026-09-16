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
    Expr, ImplItemFn, ItemImpl, Macro, Pat, Path as SynPath, Token, Type,
    parse::{Parse, ParseStream},
    visit::{self, Visit},
};

struct TyHelperRule {
    variants: &'static [&'static str],
    helper: &'static str,
    arguments: &'static str,
}

// Add mappings here when a matched type gains a dedicated query helper.
const TY_HELPER_RULES: &[TyHelperRule] = &[
    TyHelperRule {
        variants: &["Any"],
        helper: "is_any",
        arguments: "",
    },
    TyHelperRule {
        variants: &["Unknown"],
        helper: "is_unknown",
        arguments: "",
    },
    TyHelperRule {
        variants: &["Null", "Undefined"],
        helper: "is_null_or_undefined",
        arguments: "",
    },
    TyHelperRule {
        variants: &["Union"],
        helper: "is_union",
        arguments: "arena",
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
    ty_helper_rules: &'a [TyHelperRule],
    diagnostics: Vec<Diagnostic>,
    inside_ty_impl: bool,
    current_method: Option<String>,
}

impl<'a> CustomLinter<'a> {
    fn new(ty_helper_rules: &'a [TyHelperRule]) -> Self {
        Self {
            ty_helper_rules,
            diagnostics: Vec::new(),
            inside_ty_impl: false,
            current_method: None,
        }
    }

    fn check_helper_matches(&mut self, matches: &MatchesInput, span: Span) {
        if matches.guard.is_some() {
            return;
        }
        for rule in self.ty_helper_rules {
            if !(self.inside_ty_impl && self.current_method.as_deref() == Some(rule.helper))
                && rule_matches(&matches.expression, &matches.pattern, rule)
            {
                self.diagnostics.push(Diagnostic {
                    span,
                    message: format!(
                        "use `.{}({})` instead of matching on the type",
                        rule.helper, rule.arguments
                    ),
                });
            }
        }
    }
}

impl<'ast> Visit<'ast> for CustomLinter<'_> {
    fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
        let previous_inside_ty_impl = self.inside_ty_impl;
        self.inside_ty_impl = matches!(
            node.self_ty.as_ref(),
            Type::Path(self_type)
                if self_type.path.segments.last().is_some_and(|segment| segment.ident == "Ty")
        );
        visit::visit_item_impl(self, node);
        self.inside_ty_impl = previous_inside_ty_impl;
    }

    fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
        let previous_method = self.current_method.replace(node.sig.ident.to_string());
        visit::visit_impl_item_fn(self, node);
        self.current_method = previous_method;
    }

    fn visit_macro(&mut self, node: &'ast Macro) {
        if node.path.is_ident("matches")
            && let Ok(matches) = syn::parse2::<MatchesInput>(node.tokens.clone())
        {
            self.check_helper_matches(&matches, node.path.segments[0].ident.span());
        }
        visit::visit_macro(self, node);
    }
}

fn pattern_matches(pattern: &Pat, type_name: &str, variants: &[&str]) -> bool {
    if variants.len() == 1 {
        return variant_pattern_matches(pattern, type_name, variants[0]);
    }
    let Pat::Or(pattern) = pattern else {
        return false;
    };
    pattern.cases.len() == variants.len()
        && variants.iter().all(|variant| {
            pattern
                .cases
                .iter()
                .any(|case| variant_pattern_matches(case, type_name, variant))
        })
}

fn variant_pattern_matches(pattern: &Pat, type_name: &str, variant: &str) -> bool {
    match pattern {
        Pat::Path(pattern) => path_matches(&pattern.path, type_name, variant),
        Pat::TupleStruct(pattern) => {
            pattern
                .elems
                .iter()
                .all(|element| matches!(element, Pat::Wild(_)))
                && path_matches(&pattern.path, type_name, variant)
        }
        _ => false,
    }
}

fn rule_matches(expression: &Expr, pattern: &Pat, rule: &TyHelperRule) -> bool {
    if pattern_matches(pattern, "Ty", rule.variants) {
        return true;
    }
    let Expr::MethodCall(method_call) = expression else {
        return false;
    };
    method_call.method == "ty_kind"
        && method_call.args.len() == 1
        && pattern_matches(pattern, "TyKind", rule.variants)
}

fn path_matches(path: &SynPath, type_name: &str, variant: &str) -> bool {
    let mut segments = path.segments.iter().rev();
    segments
        .next()
        .is_some_and(|segment| segment.ident == variant)
        && segments
            .next()
            .is_some_and(|segment| segment.ident == type_name)
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
    let mut linter = CustomLinter::new(TY_HELPER_RULES);
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
        let mut linter = CustomLinter::new(TY_HELPER_RULES);
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
        assert_eq!(lint("fn f() { matches!(ty, Ty::Any); }")?, 1);
        assert_eq!(
            lint("fn f() { matches!(self.ty_kind(ty), TyKind::Unknown); }")?,
            1
        );
        assert_eq!(lint("fn f() { matches!(ty, Ty::Unknown); }")?, 1);
        assert_eq!(
            lint("fn f() { matches!(ty, crate::types::Ty::Unknown); }")?,
            1
        );
        assert_eq!(
            lint("fn f() { matches!(ty, Ty::Null | Ty::Undefined); }")?,
            1
        );
        assert_eq!(
            lint("fn f() { matches!(arena.ty_kind(ty), TyKind::Undefined | TyKind::Null); }")?,
            1
        );
        assert_eq!(
            lint("fn f() { !matches!(self.ty_kind(ty), TyKind::Union(_)); }")?,
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
        assert_eq!(
            lint("fn f() { matches!(ty, Ty::Null | Ty::Undefined | Ty::Void); }")?,
            0
        );
        assert_eq!(
            lint("fn f() { matches!(self.ty_kind(ty), TyKind::Union(union)); }")?,
            0
        );
        Ok(())
    }

    #[test]
    fn accepts_additional_rules() -> syn::Result<()> {
        let rules = [TyHelperRule {
            variants: &["Never"],
            helper: "is_never",
            arguments: "",
        }];
        let syntax = syn::parse_file(
            "fn f() { matches!(ty, Ty::Never); matches!(self.ty_kind(ty), TyKind::Never); }",
        )?;
        let mut linter = CustomLinter::new(&rules);
        linter.visit_file(&syntax);
        assert_eq!(linter.diagnostics.len(), 2);
        assert_eq!(
            linter.diagnostics[0].message,
            "use `.is_never()` instead of matching on the type"
        );
        Ok(())
    }

    #[test]
    fn ignores_helper_implementation() -> syn::Result<()> {
        assert_eq!(
            lint(
                "impl Ty { fn is_union(&self, arena: Arena) -> bool { matches!(arena.ty_kind(*self), TyKind::Union(_)) } }"
            )?,
            0
        );
        assert_eq!(
            lint(
                "impl Other { fn is_union(&self, arena: Arena) -> bool { matches!(arena.ty_kind(ty), TyKind::Union(_)) } }"
            )?,
            1
        );
        Ok(())
    }
}
