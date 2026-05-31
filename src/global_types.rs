use std::collections::HashMap;

use oxc_ast::AstKind;
use oxc_syntax::symbol::SymbolFlags;

use crate::{Checker, CheckerReturn, SymbolRef, Ty, program};

const ARRAY_TYPE_NAME: &str = "Array";
const READONLY_ARRAY_TYPE_NAME: &str = "ReadonlyArray";
const OBJECT_TYPE_NAME: &str = "Object";
const FUNCTION_TYPE_NAME: &str = "Function";
const STRING_TYPE_NAME: &str = "String";
const BOOLEAN_TYPE_NAME: &str = "Boolean";
const NUMBER_TYPE_NAME: &str = "Number";
const SYMBOL_TYPE_NAME: &str = "Symbol";
const BIGINT_TYPE_NAME: &str = "BigInt";

#[derive(Clone, Copy, Debug, Default)]
struct GlobalSymbolEntry {
    value_symbol: Option<SymbolRef>,
    type_symbol: Option<SymbolRef>,
}

#[derive(Debug)]
pub(crate) struct GlobalSymbolTable {
    symbols: HashMap<String, GlobalSymbolEntry>,
}

impl GlobalSymbolTable {
    pub(crate) fn new<'a>(store: &program::ProgramStore<'a>) -> Self {
        let mut table = Self {
            symbols: HashMap::new(),
        };

        for entry in store.entries() {
            let scoping = entry.semantic().scoping();
            for (_, &symbol_id) in scoping.get_bindings(scoping.root_scope_id()) {
                let flags = scoping.symbol_flags(symbol_id);
                let name = scoping.symbol_name(symbol_id);
                let symbol = SymbolRef::new(entry.id(), symbol_id);

                if flags.intersects(SymbolFlags::Value | SymbolFlags::Import) {
                    table.insert_value(name, symbol);
                }
                if flags
                    .intersects(SymbolFlags::Type | SymbolFlags::TypeImport | SymbolFlags::Import)
                {
                    table.insert_type(name, symbol);
                }
            }
        }

        table
    }

    fn insert_value(&mut self, name: &str, symbol: SymbolRef) {
        self.symbols
            .entry(name.to_string())
            .or_default()
            .value_symbol
            .get_or_insert(symbol);
    }

    fn insert_type(&mut self, name: &str, symbol: SymbolRef) {
        self.symbols
            .entry(name.to_string())
            .or_default()
            .type_symbol
            .get_or_insert(symbol);
    }

    pub(crate) fn value_symbol(&self, name: &str) -> Option<SymbolRef> {
        self.symbols.get(name).and_then(|entry| entry.value_symbol)
    }

    pub(crate) fn type_symbol(&self, name: &str) -> Option<SymbolRef> {
        self.symbols.get(name).and_then(|entry| entry.type_symbol)
    }
}

impl<'a, 'store> CheckerReturn<'a, 'store> {
    pub(crate) fn get_type_symbol_for_name(
        &self,
        program_id: program::ProgramId,
        type_name: &str,
    ) -> Option<SymbolRef> {
        self.get_type_symbol_in_program(program_id, type_name)
            .or_else(|| self.global_symbols.type_symbol(type_name))
    }

    pub(crate) fn get_value_symbol_for_name(
        &self,
        program_id: program::ProgramId,
        value_name: &str,
    ) -> Option<SymbolRef> {
        self.get_value_symbol_in_program(program_id, value_name)
            .or_else(|| self.global_symbols.value_symbol(value_name))
    }

    fn get_type_symbol_in_program(
        &self,
        program_id: program::ProgramId,
        type_name: &str,
    ) -> Option<SymbolRef> {
        self.get_root_symbol(program_id, type_name)
            .and_then(|symbol| self.get_imported_symbol(symbol).or(Some(symbol)))
            .filter(|symbol| self.symbol_has_type_meaning(*symbol))
    }

    fn get_value_symbol_in_program(
        &self,
        program_id: program::ProgramId,
        value_name: &str,
    ) -> Option<SymbolRef> {
        self.get_root_symbol(program_id, value_name)
            .and_then(|symbol| self.get_imported_symbol(symbol).or(Some(symbol)))
            .filter(|symbol| self.symbol_has_value_meaning(*symbol))
    }

    fn symbol_has_type_meaning(&self, symbol: SymbolRef) -> bool {
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        match self.nodes(symbol.program_id).kind(declaration) {
            AstKind::TSInterfaceDeclaration(_)
            | AstKind::TSTypeAliasDeclaration(_)
            | AstKind::Class(_) => true,
            AstKind::BindingIdentifier(_) => matches!(
                self.nodes(symbol.program_id).parent_kind(declaration),
                AstKind::TSInterfaceDeclaration(_)
                    | AstKind::TSTypeAliasDeclaration(_)
                    | AstKind::Class(_)
            ),
            AstKind::ImportSpecifier(_)
            | AstKind::ImportDefaultSpecifier(_)
            | AstKind::ImportNamespaceSpecifier(_) => true,
            _ => false,
        }
    }

    fn symbol_has_value_meaning(&self, symbol: SymbolRef) -> bool {
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        match self.nodes(symbol.program_id).kind(declaration) {
            AstKind::VariableDeclarator(_) | AstKind::Function(_) | AstKind::Class(_) => true,
            AstKind::BindingIdentifier(_) => matches!(
                self.nodes(symbol.program_id).parent_kind(declaration),
                AstKind::VariableDeclarator(_) | AstKind::Function(_) | AstKind::Class(_)
            ),
            AstKind::ImportSpecifier(_)
            | AstKind::ImportDefaultSpecifier(_)
            | AstKind::ImportNamespaceSpecifier(_) => true,
            _ => false,
        }
    }

    pub(crate) fn get_global_array_type_reference_type(
        &self,
        program_id: program::ProgramId,
        type_name: &str,
        type_arguments: &[Ty<'a>],
    ) -> Option<Ty<'a>> {
        let [element_type] = type_arguments else {
            return None;
        };
        let readonly = match type_name {
            ARRAY_TYPE_NAME => false,
            READONLY_ARRAY_TYPE_NAME => true,
            _ => return None,
        };
        let symbol = self.get_type_symbol_for_name(program_id, type_name)?;
        if !self
            .store
            .entry(symbol.program_id)
            .is_some_and(program::ProgramEntry::is_lib)
        {
            return None;
        }
        Some(if readonly {
            Ty::readonly_array(self.arena(), *element_type)
        } else {
            Ty::array(self.arena(), *element_type)
        })
    }

    pub(crate) fn get_global_array_type(
        &self,
        program_id: program::ProgramId,
        element_type: Ty<'a>,
    ) -> Ty<'a> {
        self.get_global_type_reference(program_id, ARRAY_TYPE_NAME, [element_type])
    }

    pub(crate) fn get_global_readonly_array_type(
        &self,
        program_id: program::ProgramId,
        element_type: Ty<'a>,
    ) -> Ty<'a> {
        self.get_global_type_reference(program_id, READONLY_ARRAY_TYPE_NAME, [element_type])
    }

    pub(crate) fn get_global_object_type(&self, program_id: program::ProgramId) -> Ty<'a> {
        self.get_global_type(program_id, OBJECT_TYPE_NAME)
    }

    pub(crate) fn get_global_function_type(&self, program_id: program::ProgramId) -> Ty<'a> {
        self.get_global_type(program_id, FUNCTION_TYPE_NAME)
    }

    pub(crate) fn get_global_string_type(&self, program_id: program::ProgramId) -> Ty<'a> {
        self.get_global_type(program_id, STRING_TYPE_NAME)
    }

    pub(crate) fn get_global_boolean_type(&self, program_id: program::ProgramId) -> Ty<'a> {
        self.get_global_type(program_id, BOOLEAN_TYPE_NAME)
    }

    pub(crate) fn get_global_number_type(&self, program_id: program::ProgramId) -> Ty<'a> {
        self.get_global_type(program_id, NUMBER_TYPE_NAME)
    }

    pub(crate) fn get_global_symbol_type(&self, program_id: program::ProgramId) -> Ty<'a> {
        self.get_global_type(program_id, SYMBOL_TYPE_NAME)
    }

    pub(crate) fn get_global_bigint_type(&self, program_id: program::ProgramId) -> Ty<'a> {
        self.get_global_type(program_id, BIGINT_TYPE_NAME)
    }

    pub(crate) fn get_global_promise_type(&self, program_id: program::ProgramId) -> Ty<'a> {
        self.get_global_type(program_id, "Promise")
    }

    pub(crate) fn get_global_type(&self, program_id: program::ProgramId, name: &str) -> Ty<'a> {
        self.get_global_type_reference(program_id, name, std::iter::empty())
    }

    fn get_global_type_reference(
        &self,
        program_id: program::ProgramId,
        name: &str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Ty<'a> {
        if self.get_type_symbol_for_name(program_id, name).is_none() {
            return Ty::any();
        }

        Ty::type_reference(self.arena(), self.arena().str(name), type_arguments)
    }
}
