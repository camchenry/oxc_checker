use std::collections::HashMap;

use oxc_ast::{AstKind, ast::Expression};
use oxc_semantic::NodeId;
use oxc_syntax::symbol::SymbolFlags;

use crate::{
    checker::{CheckerReturn, SymbolRef},
    checker_impl::UNDEFINED_IDENT,
    program,
    types::{Ty, TyTypeReference},
};

const ARRAY_TYPE_NAME: &str = "Array";
const READONLY_ARRAY_TYPE_NAME: &str = "ReadonlyArray";
const OBJECT_TYPE_NAME: &str = "Object";
const FUNCTION_TYPE_NAME: &str = "Function";
const CALLABLE_FUNCTION_TYPE_NAME: &str = "CallableFunction";
const NEWABLE_FUNCTION_TYPE_NAME: &str = "NewableFunction";
const STRING_TYPE_NAME: &str = "String";
const BOOLEAN_TYPE_NAME: &str = "Boolean";
const NUMBER_TYPE_NAME: &str = "Number";
const SYMBOL_TYPE_NAME: &str = "Symbol";
const BIGINT_TYPE_NAME: &str = "BigInt";
const REGEXP_TYPE_NAME: &str = "RegExp";
const AWAITED_TYPE_NAME: &str = "Awaited";
const NON_NULLABLE_TYPE_NAME: &str = "NonNullable";
const EXTRACT_TYPE_NAME: &str = "Extract";
const RECORD_TYPE_NAME: &str = "Record";
const GENERATOR_TYPE_NAME: &str = "Generator";
const ASYNC_GENERATOR_TYPE_NAME: &str = "AsyncGenerator";

#[derive(Clone, Copy, Debug, Default)]
struct GlobalSymbolEntry {
    value_symbol: Option<SymbolRef>,
    global_this_value_symbol: Option<SymbolRef>,
    type_symbol: Option<SymbolRef>,
}

#[derive(Debug)]
pub struct GlobalSymbolTable {
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
                if (entry.is_lib() || !entry.module_record().has_module_syntax)
                    && flags.intersects(SymbolFlags::Value)
                    && !flags.intersects(SymbolFlags::BlockScoped)
                {
                    table.insert_global_this_value(name, symbol);
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

    fn insert_global_this_value(&mut self, name: &str, symbol: SymbolRef) {
        self.symbols
            .entry(name.to_string())
            .or_default()
            .global_this_value_symbol
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

    pub(crate) fn global_this_value_symbol(&self, name: &str) -> Option<SymbolRef> {
        self.symbols
            .get(name)
            .and_then(|entry| entry.global_this_value_symbol)
    }

    pub(crate) fn global_this_value_symbols(&self) -> impl Iterator<Item = (&str, SymbolRef)> {
        self.symbols.iter().filter_map(|(name, entry)| {
            entry
                .global_this_value_symbol
                .map(|symbol| (name.as_str(), symbol))
        })
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

    pub(crate) fn get_type_symbol_and_declaration_for_name(
        &self,
        program_id: program::ProgramId,
        type_name: &str,
    ) -> Option<(SymbolRef, NodeId)> {
        let symbol = self.get_type_symbol_for_name(program_id, type_name)?;
        let declaration = self
            .semantic(symbol.program_id)
            .scoping()
            .symbol_declaration(symbol.symbol_id);
        Some((symbol, declaration))
    }

    pub fn get_value_symbol_for_name(
        &self,
        program_id: program::ProgramId,
        value_name: &str,
    ) -> Option<SymbolRef> {
        self.get_value_symbol_in_program(program_id, value_name)
            .or_else(|| self.global_symbols.value_symbol(value_name))
    }

    pub(crate) fn is_global_undefined_expression(
        &self,
        program_id: program::ProgramId,
        expression: &Expression<'_>,
    ) -> bool {
        let Expression::Identifier(identifier) = expression else {
            return false;
        };
        if identifier.name != UNDEFINED_IDENT {
            return false;
        }
        identifier.reference_id.get().is_none_or(|reference_id| {
            self.semantic(program_id)
                .scoping()
                .get_reference(reference_id)
                .symbol_id()
                .is_none()
        })
    }

    pub(crate) fn get_type_symbol_in_program(
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
            | AstKind::TSEnumDeclaration(_)
            | AstKind::Class(_) => true,
            AstKind::BindingIdentifier(_) => matches!(
                self.nodes(symbol.program_id).parent_kind(declaration),
                AstKind::TSInterfaceDeclaration(_)
                    | AstKind::TSTypeAliasDeclaration(_)
                    | AstKind::TSEnumDeclaration(_)
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
        Some(Ty::generic_array(self.arena(), *element_type, readonly))
    }

    pub(crate) fn get_global_array_type(
        &self,
        program_id: program::ProgramId,
        element_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, ARRAY_TYPE_NAME, [element_type])
    }

    pub(crate) fn get_global_readonly_array_type(
        &self,
        program_id: program::ProgramId,
        element_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, READONLY_ARRAY_TYPE_NAME, [element_type])
    }

    pub(crate) fn get_global_object_type(&self, program_id: program::ProgramId) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, OBJECT_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_function_type(
        &self,
        program_id: program::ProgramId,
    ) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, FUNCTION_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_callable_function_type(
        &self,
        program_id: program::ProgramId,
    ) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, CALLABLE_FUNCTION_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_newable_function_type(
        &self,
        program_id: program::ProgramId,
    ) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, NEWABLE_FUNCTION_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_string_type(&self, program_id: program::ProgramId) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, STRING_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_boolean_type(&self, program_id: program::ProgramId) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, BOOLEAN_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_number_type(&self, program_id: program::ProgramId) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, NUMBER_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_symbol_type(&self, program_id: program::ProgramId) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, SYMBOL_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_bigint_type(&self, program_id: program::ProgramId) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, BIGINT_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_regexp_type(&self, program_id: program::ProgramId) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, REGEXP_TYPE_NAME, std::iter::empty())
    }

    pub(crate) fn get_global_promise_type(&self, program_id: program::ProgramId) -> Option<Ty<'a>> {
        self.get_global_type_reference(program_id, "Promise", std::iter::empty())
    }

    pub(crate) fn get_global_awaited_type(
        &self,
        program_id: program::ProgramId,
        awaited_type: Ty<'a>,
    ) -> Ty<'a> {
        if !self.is_default_lib_type(program_id, AWAITED_TYPE_NAME) {
            return Ty::any();
        }
        Ty::type_reference(self.arena(), AWAITED_TYPE_NAME, [awaited_type])
    }

    pub(crate) fn get_global_non_nullable_type(
        &self,
        program_id: program::ProgramId,
        target_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        self.is_default_lib_type(program_id, NON_NULLABLE_TYPE_NAME)
            .then(|| Ty::type_reference(self.arena(), NON_NULLABLE_TYPE_NAME, [target_type]))
    }

    pub(crate) fn get_global_extract_type(
        &self,
        program_id: program::ProgramId,
        target_type: Ty<'a>,
        constraint_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        self.is_default_lib_type(program_id, EXTRACT_TYPE_NAME)
            .then(|| {
                Ty::type_reference(
                    self.arena(),
                    EXTRACT_TYPE_NAME,
                    [target_type, constraint_type],
                )
            })
    }

    pub(crate) fn get_global_generator_type(
        &self,
        program_id: program::ProgramId,
        yield_type: Ty<'a>,
        return_type: Ty<'a>,
        next_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        self.get_global_type_reference(
            program_id,
            GENERATOR_TYPE_NAME,
            [yield_type, return_type, next_type],
        )
    }

    pub(crate) fn get_global_async_generator_type(
        &self,
        program_id: program::ProgramId,
        yield_type: Ty<'a>,
        return_type: Ty<'a>,
        next_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        self.get_global_type_reference(
            program_id,
            ASYNC_GENERATOR_TYPE_NAME,
            [yield_type, return_type, next_type],
        )
    }

    pub(crate) fn get_global_record_type(
        &self,
        program_id: program::ProgramId,
        key_type: Ty<'a>,
        value_type: Ty<'a>,
    ) -> Option<Ty<'a>> {
        self.is_default_lib_type(program_id, RECORD_TYPE_NAME)
            .then(|| Ty::type_reference(self.arena(), RECORD_TYPE_NAME, [key_type, value_type]))
    }

    pub(crate) fn is_global_awaited_type_reference(
        &self,
        program_id: program::ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> bool {
        reference.name == AWAITED_TYPE_NAME
            && reference.type_arguments.len() == 1
            && self.is_default_lib_type(program_id, AWAITED_TYPE_NAME)
    }

    pub(crate) fn is_global_non_nullable_type_reference(
        &self,
        program_id: program::ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> bool {
        reference.name == NON_NULLABLE_TYPE_NAME
            && reference.type_arguments.len() == 1
            && self.is_default_lib_type(program_id, NON_NULLABLE_TYPE_NAME)
    }

    pub(crate) fn is_global_regexp_type_reference(
        &self,
        program_id: program::ProgramId,
        reference: &TyTypeReference<'a>,
    ) -> bool {
        reference.name == REGEXP_TYPE_NAME
            && reference.is_bare()
            && self.is_default_lib_type(program_id, REGEXP_TYPE_NAME)
    }

    fn is_default_lib_type(&self, program_id: program::ProgramId, name: &str) -> bool {
        self.get_type_symbol_for_name(program_id, name)
            .is_some_and(|symbol| {
                self.store
                    .entry(symbol.program_id)
                    .is_some_and(program::ProgramEntry::is_lib)
            })
    }

    pub(crate) fn get_global_type_reference(
        &self,
        program_id: program::ProgramId,
        name: &str,
        type_arguments: impl IntoIterator<Item = Ty<'a>>,
    ) -> Option<Ty<'a>> {
        self.get_type_symbol_for_name(program_id, name)?;

        Some(Ty::type_reference(
            self.arena(),
            self.arena().str(name),
            type_arguments,
        ))
    }
}
