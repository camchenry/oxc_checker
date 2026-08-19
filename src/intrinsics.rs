use crate::{
    TemplateLiteralElement,
    checker::Checker,
    limits::TYPE_EXPANSION_MAX_DEPTH,
    types::{Ty, TyKind},
};

fn capitalize_first_character(value: &str, uppercase: bool) -> String {
    let Some(first) = value.chars().next() else {
        return String::new();
    };
    let first_len = first.len_utf8();
    let mut mapped = if uppercase {
        first.to_uppercase().collect::<String>()
    } else {
        first.to_lowercase().collect::<String>()
    };
    mapped.push_str(&value[first_len..]);
    mapped
}

impl<'a, 'store> Checker<'a, 'store> {
    pub(super) fn get_type_from_intrinsic_alias(
        &self,
        program_id: crate::program::ProgramId,
        name: &'a str,
        type_arguments: &[Ty<'a>],
        depth: usize,
    ) -> Ty<'a> {
        let Some(type_argument) = type_arguments.first().copied() else {
            return self.ty.type_reference("intrinsic", std::iter::empty());
        };

        match name {
            "Uppercase" | "Lowercase" | "Capitalize" | "Uncapitalize" => {
                self.apply_intrinsic_string_mapping(program_id, name, type_argument, depth + 1)
            }
            "NoInfer" => type_argument,
            "BuiltinIteratorReturn" => self.ty.any(),
            _ => self.ty.type_reference("intrinsic", std::iter::empty()),
        }
    }

    fn apply_intrinsic_string_mapping(
        &self,
        program_id: crate::program::ProgramId,
        name: &'a str,
        ty: Ty<'a>,
        depth: usize,
    ) -> Ty<'a> {
        if depth >= TYPE_EXPANSION_MAX_DEPTH {
            return ty;
        }

        match self.ty_kind(ty) {
            TyKind::Union(union) => {
                self.ty.union(union.types.iter().map(|ty| {
                    self.apply_intrinsic_string_mapping(program_id, name, *ty, depth + 1)
                }))
            }
            TyKind::StringLiteral(literal) => {
                self.arena()
                    .string_literal(self.apply_intrinsic_string_mapping_to_string(
                        name,
                        literal.value,
                        matches!(name, "Capitalize" | "Uncapitalize"),
                    ))
            }
            TyKind::TemplateLiteral(template) => {
                let mut quasis = template
                    .quasis
                    .iter()
                    .map(|quasi| TemplateLiteralElement { value: quasi.value })
                    .collect::<Vec<_>>();
                let mut expressions = template.expressions.iter().copied().collect::<Vec<_>>();

                match name {
                    "Uppercase" | "Lowercase" => {
                        for quasi in &mut quasis {
                            quasi.value = self.apply_intrinsic_string_mapping_to_string(
                                name,
                                quasi.value,
                                false,
                            );
                        }
                        for expression in &mut expressions {
                            *expression = self.apply_intrinsic_string_mapping(
                                program_id,
                                name,
                                *expression,
                                depth + 1,
                            );
                        }
                    }
                    "Capitalize" | "Uncapitalize" => {
                        if quasis.first().is_some_and(|quasi| quasi.value.is_empty()) {
                            if let Some(expression) = expressions.first_mut() {
                                *expression = self.apply_intrinsic_string_mapping(
                                    program_id,
                                    name,
                                    *expression,
                                    depth + 1,
                                );
                            }
                        } else if let Some(quasi) = quasis.first_mut() {
                            quasi.value = self.apply_intrinsic_string_mapping_to_string(
                                name,
                                quasi.value,
                                true,
                            );
                        }
                    }
                    _ => {}
                }

                self.get_template_literal_type(program_id, quasis, expressions)
            }
            TyKind::TypeReference(reference) if reference.name == name => ty,
            TyKind::TypeReference(_) => {
                let expanded = self.expand_type(program_id, ty, depth + 1);
                if expanded != ty {
                    self.apply_intrinsic_string_mapping(program_id, name, expanded, depth + 1)
                } else {
                    self.ty.type_reference(name, [ty])
                }
            }
            TyKind::String | TyKind::Any | TyKind::Error(_) | TyKind::Unknown => {
                self.ty.type_reference(name, [ty])
            }
            _ => ty,
        }
    }

    fn apply_intrinsic_string_mapping_to_string(
        &self,
        name: &str,
        value: &str,
        first_character_only: bool,
    ) -> &'a str {
        let mapped = match name {
            "Uppercase" => {
                if first_character_only {
                    capitalize_first_character(value, true)
                } else {
                    value.to_uppercase()
                }
            }
            "Lowercase" => value.to_lowercase(),
            "Capitalize" => capitalize_first_character(value, true),
            "Uncapitalize" => capitalize_first_character(value, false),
            _ => value.to_string(),
        };
        self.arena().str(&mapped)
    }
}
