use oxc_ast::ast::Program;
use oxc_semantic::{SemanticBuilder, SymbolId};
use oxc_span::GetSpan;

// TODO: Make use of the same pattern in oxc_ast for ast node types
#[derive(Debug, PartialEq, Eq, Clone)]
enum Ty {
    None,
    Number,
    String,
    Boolean,
}

struct CheckerBuilder {}

impl CheckerBuilder {
    fn new() -> Self {
        Self {}
    }

    fn build(&self, _program: &Program) -> CheckerReturn {
        CheckerReturn {}
    }
}

struct CheckerReturn {}

impl CheckerReturn {
    fn get_type_of_symbol(&self, sym: SymbolId) -> Ty {
        Ty::None
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use oxc_allocator::Allocator;
    use oxc_ast::ast::Statement;
    use oxc_parser::Parser;
    use oxc_span::SourceType;

    #[test]
    fn it_works() {
        let allocator = Allocator::default();
        let source_text = "const a: number = 1;";
        let parser = Parser::new(&allocator, source_text, SourceType::ts());
        let ret = parser.parse();
        assert!(ret.errors.is_empty());

        let semantic = SemanticBuilder::new();
        let program = &ret.program;
        let semantic_ret = semantic.build(program);

        let checker = CheckerBuilder::new();
        let checker_ret = checker.build(program);
        let Statement::VariableDeclaration(var_decl) = &program.body[0] else {
            return;
        };
        let symbol_id = var_decl.declarations[0]
            .id
            .get_binding_identifier()
            .unwrap()
            .symbol_id();
        assert_eq!(checker_ret.get_type_of_symbol(symbol_id), Ty::Number);
    }
}
