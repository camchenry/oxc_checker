#![allow(dead_code, unused_imports)]
use oxc_ast::{
    AstKind,
    ast::{Program, TSType, TSTypeAnnotation},
};
use oxc_index::nonmax::NonMaxU32;
use oxc_semantic::{AstNode, AstNodes, NodeId, Semantic, SemanticBuilder, SymbolId};
use oxc_span::GetSpan;

// TODO: Make use of the same pattern in oxc_ast for ast node types
#[derive(Debug, PartialEq, Eq, Clone)]
enum Ty {
    None,
    Number,
    String,
    Boolean,
}

impl Ty {
    fn from_ts_type_annotation(type_annotation: Option<&TSTypeAnnotation<'_>>) -> Self {
        type_annotation.map_or(Self::None, |type_annotation| {
            Self::from_ts_type(&type_annotation.type_annotation)
        })
    }

    fn from_ts_type(t: &TSType<'_>) -> Self {
        match t {
            TSType::TSNumberKeyword(_) => Self::Number,
            TSType::TSStringKeyword(_) => Self::String,
            TSType::TSBooleanKeyword(_) => Self::Boolean,
            TSType::TSParenthesizedType(parenthesized) => {
                Self::from_ts_type(&parenthesized.type_annotation)
            }
            TSType::TSAnyKeyword(tsany_keyword) => todo!(),
            TSType::TSBigIntKeyword(tsbig_int_keyword) => todo!(),
            TSType::TSIntrinsicKeyword(tsintrinsic_keyword) => todo!(),
            TSType::TSNeverKeyword(tsnever_keyword) => todo!(),
            TSType::TSNullKeyword(tsnull_keyword) => todo!(),
            TSType::TSObjectKeyword(tsobject_keyword) => todo!(),
            TSType::TSSymbolKeyword(tssymbol_keyword) => todo!(),
            TSType::TSUndefinedKeyword(tsundefined_keyword) => todo!(),
            TSType::TSUnknownKeyword(tsunknown_keyword) => todo!(),
            TSType::TSVoidKeyword(tsvoid_keyword) => todo!(),
            TSType::TSArrayType(tsarray_type) => todo!(),
            TSType::TSConditionalType(tsconditional_type) => todo!(),
            TSType::TSConstructorType(tsconstructor_type) => todo!(),
            TSType::TSFunctionType(tsfunction_type) => todo!(),
            TSType::TSImportType(tsimport_type) => todo!(),
            TSType::TSIndexedAccessType(tsindexed_access_type) => todo!(),
            TSType::TSInferType(tsinfer_type) => todo!(),
            TSType::TSIntersectionType(tsintersection_type) => todo!(),
            TSType::TSLiteralType(tsliteral_type) => todo!(),
            TSType::TSMappedType(tsmapped_type) => todo!(),
            TSType::TSNamedTupleMember(tsnamed_tuple_member) => todo!(),
            TSType::TSTemplateLiteralType(tstemplate_literal_type) => todo!(),
            TSType::TSThisType(tsthis_type) => todo!(),
            TSType::TSTupleType(tstuple_type) => todo!(),
            TSType::TSTypeLiteral(tstype_literal) => todo!(),
            TSType::TSTypeOperatorType(tstype_operator) => todo!(),
            TSType::TSTypePredicate(tstype_predicate) => todo!(),
            TSType::TSTypeQuery(tstype_query) => todo!(),
            TSType::TSTypeReference(tstype_reference) => todo!(),
            TSType::TSUnionType(tsunion_type) => todo!(),
            TSType::JSDocNullableType(jsdoc_nullable_type) => todo!(),
            TSType::JSDocNonNullableType(jsdoc_non_nullable_type) => todo!(),
            TSType::JSDocUnknownType(jsdoc_unknown_type) => todo!(),
        }
    }
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

    fn build<'a>(&self, program: &'a Program<'a>, semantic: Semantic<'a>) -> CheckerReturn<'a> {
        CheckerReturn { program, semantic }
    }
}

struct CheckerReturn<'a> {
    program: &'a Program<'a>,
    semantic: Semantic<'a>,
}

impl<'a> CheckerReturn<'a> {
    #[inline]
    fn program(&self) -> &'a Program<'a> {
        self.program
    }

    #[inline]
    fn semantic(&self) -> &Semantic<'a> {
        &self.semantic
    }

    #[inline]
    fn nodes(&self) -> &AstNodes<'a> {
        self.semantic.nodes()
    }

    #[inline]
    fn node_kind(&self, node: NodeId) -> AstKind<'a> {
        self.nodes().kind(node)
    }
}

impl Checker for CheckerReturn<'_> {
    fn get_symbol_at_location(&self, node: NodeId) -> Option<SymbolId> {
        match self.node_kind(node) {
            AstKind::BindingIdentifier(identifier) => identifier.symbol_id.get(),
            AstKind::IdentifierReference(identifier) => {
                identifier.reference_id.get().and_then(|reference_id| {
                    self.semantic
                        .scoping()
                        .get_reference(reference_id)
                        .symbol_id()
                })
            }
            _ => None,
        }
    }

    fn get_type_at_location(&self, node: NodeId) -> Ty {
        self.get_symbol_at_location(node)
            .map_or(Ty::None, |sym| self.get_type_of_symbol(sym))
    }

    fn get_declared_type_of_symbol(&self, sym: SymbolId) -> Ty {
        match self.semantic().symbol_declaration(sym).kind() {
            AstKind::VariableDeclarator(declarator) => {
                Ty::from_ts_type_annotation(declarator.type_annotation.as_deref())
            }
            AstKind::FormalParameter(parameter) => {
                Ty::from_ts_type_annotation(parameter.type_annotation.as_deref())
            }
            AstKind::FormalParameterRest(parameter) => {
                Ty::from_ts_type_annotation(parameter.type_annotation.as_deref())
            }
            AstKind::CatchParameter(parameter) => {
                Ty::from_ts_type_annotation(parameter.type_annotation.as_deref())
            }
            AstKind::PropertyDefinition(property) => {
                Ty::from_ts_type_annotation(property.type_annotation.as_deref())
            }
            AstKind::AccessorProperty(property) => {
                Ty::from_ts_type_annotation(property.type_annotation.as_deref())
            }
            _ => Ty::None,
        }
    }

    fn get_type_of_symbol(&self, sym: SymbolId) -> Ty {
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
        self.get_declared_type_of_symbol(sym)
    }

    fn get_type_of_symbol_at_location(&self, node: NodeId) -> Ty {
        self.get_type_at_location(node)
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

    fn type_to_string(&self, t: Ty, _location: NodeId) -> String {
        match t {
            Ty::None => "none",
            Ty::Number => "number",
            Ty::String => "string",
            Ty::Boolean => "boolean",
        }
        .to_string()
    }

    fn symbol_to_string(&self, s: SymbolId, _location: NodeId) -> String {
        self.semantic().scoping().symbol_name(s).to_string()
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

        let program = &ret.program;
        let semantic_ret = SemanticBuilder::new().build(program);
        assert!(semantic_ret.errors.is_empty());

        let checker = CheckerBuilder::new();
        let checker_ret = checker.build(program, semantic_ret.semantic);
        assert!(std::ptr::eq(checker_ret.program(), program));
        assert_eq!(
            checker_ret.semantic().nodes().program().source_text,
            source_text
        );
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
