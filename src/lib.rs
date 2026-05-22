#![allow(dead_code, unused_imports)]
use oxc_ast::ast::Program;
use oxc_index::nonmax::NonMaxU32;
use oxc_semantic::{AstNode, NodeId, SemanticBuilder, SymbolId};
use oxc_span::GetSpan;

// TODO: Make use of the same pattern in oxc_ast for ast node types
#[derive(Debug, PartialEq, Eq, Clone)]
enum Ty {
    None,
    Number,
    String,
    Boolean,
}

/*

type Signature struct {
    flags                    SignatureFlags
    minArgumentCount         int32
    resolvedMinArgumentCount int32
    declaration              *ast.Node
    typeParameters           []*Type
    parameters               []*ast.Symbol
    thisParameter            *ast.Symbol
    resolvedReturnType       *Type
    resolvedTypePredicate    *TypePredicate
    target                   *Signature
    mapper                   *TypeMapper
    isolatedSignatureType    *Type
    composite                *CompositeSignature
}

type Checker interface {
    CheckFile(ctx context.Context, file *SourceFile) []Diagnostic
    GetGlobalDiagnostics() []Diagnostic

    GetSymbolAtLocation(node *Node) *Symbol
    GetTypeAtLocation(node *Node) *Type
    GetTypeFromTypeNode(node *Node) *Type

    GetDeclaredTypeOfSymbol(symbol *Symbol) *Type
    GetTypeOfSymbol(symbol *Symbol) *Type
    GetTypeOfSymbolAtLocation(symbol *Symbol, location *Node) *Type

    GetPropertiesOfType(t *Type) []*Symbol
    GetPropertyOfType(t *Type, name string) *Symbol
    GetSignaturesOfType(t *Type, kind SignatureKind) []*Signature
    GetIndexInfosOfType(t *Type) []*IndexInfo

    IsAssignableTo(source, target *Type) bool
    TypeToString(t *Type, location *Node) string
    SymbolToString(s *Symbol, location *Node) string
}

*/

enum SignatureKind {
    Call,
    Construct,
}
struct Signature {}
struct IndexInfo {}

trait Checker {
    fn get_symbol_at_location(&self, node: NodeId) -> Option<SymbolId>;
    fn get_type_at_location(&self, node: NodeId) -> Ty;
    // fn get_type_from_type_node(&self, type_node: NodeId) -> Ty;
    fn get_declared_type_of_symbol(&self, sym: SymbolId) -> Ty;
    fn get_type_of_symbol(&self, sym: SymbolId) -> Ty;
    fn get_type_of_symbol_at_location(&self, node: NodeId) -> Ty;
    fn get_properties_of_type(&self, t: Ty) -> Vec<SymbolId>;
    fn get_property_of_type(&self, t: Ty, name: &str) -> Option<SymbolId>;
    fn get_signatures_of_type(&self, t: Ty, kind: SignatureKind) -> Vec<Signature>;
    fn get_index_infos_of_type(&self, t: Ty) -> Vec<IndexInfo>;
    fn is_assignable_to(&self, source: Ty, target: Ty) -> bool;
    fn type_to_string(&self, t: Ty, location: NodeId) -> String;
    fn symbol_to_string(&self, s: SymbolId, location: NodeId) -> String;
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

impl CheckerReturn {}

impl Checker for CheckerReturn {
    fn get_symbol_at_location(&self, _node: NodeId) -> Option<SymbolId> {
        None
    }

    fn get_type_at_location(&self, _node: NodeId) -> Ty {
        Ty::None
    }

    fn get_declared_type_of_symbol(&self, _sym: SymbolId) -> Ty {
        Ty::None
    }

    fn get_type_of_symbol(&self, _sym: SymbolId) -> Ty {
        /*
        if symbol.CheckFlags&ast.CheckFlagsDeferredType != 0 {
            return c.getTypeOfSymbolWithDeferredType(symbol)
        }
        if symbol.CheckFlags&ast.CheckFlagsInstantiated != 0 {
            return c.getTypeOfInstantiatedSymbol(symbol)
        }
        if symbol.CheckFlags&ast.CheckFlagsMapped != 0 {
            return c.getTypeOfMappedSymbol(symbol)
        }
        if symbol.CheckFlags&ast.CheckFlagsReverseMapped != 0 {
            return c.getTypeOfReverseMappedSymbol(symbol)
        }
        if symbol.Flags&(ast.SymbolFlagsVariable|ast.SymbolFlagsProperty) != 0 {
            return c.getTypeOfVariableOrParameterOrProperty(symbol)
        }
        if symbol.Flags&(ast.SymbolFlagsFunction|ast.SymbolFlagsMethod|ast.SymbolFlagsClass|ast.SymbolFlagsEnum|ast.SymbolFlagsValueModule) != 0 {
            return c.getTypeOfFuncClassEnumModule(symbol)
        }
        if symbol.Flags&ast.SymbolFlagsEnumMember != 0 {
            return c.getTypeOfEnumMember(symbol)
        }
        if symbol.Flags&ast.SymbolFlagsAccessor != 0 {
            return c.getTypeOfAccessors(symbol)
        }
        if symbol.Flags&ast.SymbolFlagsAlias != 0 {
            return c.getTypeOfAlias(symbol)
        }
        return c.errorType
            */
        Ty::None
    }

    fn get_type_of_symbol_at_location(&self, _node: NodeId) -> Ty {
        Ty::None
    }

    fn get_properties_of_type(&self, _t: Ty) -> Vec<SymbolId> {
        Vec::new()
    }

    fn get_property_of_type(&self, _t: Ty, _name: &str) -> Option<SymbolId> {
        None
    }

    fn get_signatures_of_type(&self, _t: Ty, _kind: SignatureKind) -> Vec<Signature> {
        Vec::new()
    }

    fn get_index_infos_of_type(&self, _t: Ty) -> Vec<IndexInfo> {
        Vec::new()
    }

    fn is_assignable_to(&self, _source: Ty, _target: Ty) -> bool {
        false
    }

    fn type_to_string(&self, _t: Ty, _location: NodeId) -> String {
        String::new()
    }

    fn symbol_to_string(&self, _s: SymbolId, _location: NodeId) -> String {
        String::new()
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
