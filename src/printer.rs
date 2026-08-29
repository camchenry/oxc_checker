use bitflags::bitflags;
use num_traits::Zero;
use oxc_syntax::identifier::is_identifier_name;
use std::cell::Cell;

use crate::{
    checker::Checker,
    limits::TYPE_STRING_MAX_DEPTH,
    types::{
        MappedModifier, Signature, SignatureKind, TupleElement, Ty, TyFunction, TyKind,
        TyParameter, TyProperty, TyPropertyFlags, TyTypeParameter, TyTypePredicate,
    },
};

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct TypeFormatFlags: u8 {
        const NONE = 0;
        const WRITE_ARRAY_AS_GENERIC_TYPE = 1 << 0;
        const PRESERVE_PROPERTY_NAME_QUOTES = 1 << 1;
        const USE_SINGLE_QUOTES_FOR_STRING_LITERAL = 1 << 2;
        const PARENTHESIZE_CONDITIONAL_RETURN = 1 << 3;
    }
}

pub(crate) struct TypePrinter<'checker, 'a, 'store> {
    checker: &'checker Checker<'a, 'store>,
}

impl<'checker, 'a, 'store> TypePrinter<'checker, 'a, 'store> {
    pub(crate) fn new(checker: &'checker Checker<'a, 'store>) -> Self {
        Self { checker }
    }

    pub(crate) fn to_type_string(&self, ty: Ty<'a>) -> String {
        let depth = Cell::new(0);
        self.to_type_string_with_depth(ty, &|_| None, &depth)
    }

    pub(crate) fn to_type_string_with_depth(
        &self,
        ty: Ty<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        depth: &Cell<usize>,
    ) -> String {
        self.to_type_string_with_flags(
            ty,
            replace_type_reference,
            TypeFormatFlags::PRESERVE_PROPERTY_NAME_QUOTES,
            depth,
        )
    }

    fn to_type_string_with_flags(
        &self,
        ty: Ty<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let current = depth.get();
        if current >= TYPE_STRING_MAX_DEPTH {
            return "...".to_string();
        }

        let flags = if current == 0 {
            flags
        } else {
            flags & !TypeFormatFlags::PRESERVE_PROPERTY_NAME_QUOTES
        };
        depth.set(current + 1);
        let result = self.to_type_string_inner(ty, replace_type_reference, flags, depth);
        depth.set(current);
        result
    }

    fn to_type_string_inner(
        &self,
        ty: Ty<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let arena = self.checker.arena();
        match self.checker.ty_kind(ty) {
            TyKind::None => "none".to_string(),
            TyKind::Number => "number".to_string(),
            TyKind::String => "string".to_string(),
            TyKind::Boolean => "boolean".to_string(),
            TyKind::Bigint => "bigint".to_string(),
            TyKind::Symbol => "symbol".to_string(),
            TyKind::UniqueSymbol(_) => "unique symbol".to_string(),
            TyKind::Undefined => "undefined".to_string(),
            TyKind::Null => "null".to_string(),
            TyKind::Any => "any".to_string(),
            TyKind::Error(_) => "any".to_string(),
            TyKind::Unknown => "unknown".to_string(),
            TyKind::Void => "void".to_string(),
            TyKind::Never => "never".to_string(),
            TyKind::PrimitiveObject => "object".to_string(),
            TyKind::This => "this".to_string(),
            TyKind::Object(object) => {
                if object.is_constructor_type
                    && let Some(signature) = object.signatures().first()
                {
                    return self.constructor_type_to_string(*signature, &|_| None, flags, depth);
                }
                if object.properties.is_empty()
                    && object.signatures().is_empty()
                    && object.index_infos().is_empty()
                {
                    return "{}".to_string();
                }

                let signatures = object
                    .signatures()
                    .iter()
                    .filter(|signature| signature.kind == SignatureKind::Call)
                    .chain(
                        object
                            .signatures()
                            .iter()
                            .filter(|signature| signature.kind == SignatureKind::Construct),
                    );
                let members = signatures
                    .map(|signature| {
                        self.signature_to_type_string(*signature, &|_| None, flags, depth)
                    })
                    .chain(object.index_infos().iter().map(|info| {
                        let readonly = if info.readonly { "readonly " } else { "" };
                        format!(
                            "{}[{}: {}]: {};",
                            readonly,
                            info.name,
                            self.to_type_string_with_flags(
                                info.key_type,
                                replace_type_reference,
                                flags,
                                depth,
                            ),
                            self.to_type_string_with_flags(
                                info.value_type,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        )
                    }))
                    .chain(object.properties.iter().map(|property| {
                        let readonly = if property.readonly { "readonly " } else { "" };
                        if property.method
                            && let TyKind::Function(function) = arena.ty_kind(property.ty)
                        {
                            format!(
                                "{}{}{};",
                                readonly,
                                property_name_to_type_string(property, flags),
                                self.signature_to_type_string_for_function(
                                    function,
                                    &|_| None,
                                    flags,
                                    depth,
                                )
                            )
                        } else {
                            format!(
                                "{}{}: {};",
                                readonly,
                                property_name_to_type_string(property, flags),
                                self.to_type_string_with_flags(
                                    property.ty,
                                    replace_type_reference,
                                    flags
                                        | TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE
                                        | if property
                                            .flags
                                            .contains(TyPropertyFlags::TYPE_SINGLE_QUOTED)
                                        {
                                            TypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL
                                        } else {
                                            TypeFormatFlags::NONE
                                        },
                                    depth,
                                )
                            )
                        }
                    }))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("{{ {members} }}")
            }
            TyKind::ModuleNamespace(namespace) => format!("typeof {}", namespace.name),
            TyKind::Function(function) => {
                self.function_type_to_string(function, &|_| None, flags, depth)
            }
            TyKind::TypeReference(reference) => {
                if let Some(replacement) = replace_type_reference(ty)
                    && replacement != ty
                {
                    return self.to_type_string_with_flags(
                        replacement,
                        replace_type_reference,
                        flags,
                        depth,
                    );
                }
                if reference.display_type_argument_count == 0 {
                    reference.name.to_string()
                } else {
                    let type_arguments = reference
                        .type_arguments
                        .iter()
                        .take(reference.display_type_argument_count)
                        .map(|ty| {
                            self.to_type_string_with_flags(
                                *ty,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{type_arguments}>", reference.name)
                }
            }
            TyKind::Class(class) => format!("typeof {}", class.name),
            TyKind::TypeQuery(query) => {
                if query.type_arguments.is_empty() {
                    format!("typeof {}", query.name)
                } else {
                    let type_arguments = query
                        .type_arguments
                        .iter()
                        .map(|ty| {
                            self.to_type_string_with_flags(
                                *ty,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("typeof {}<{type_arguments}>", query.name)
                }
            }
            TyKind::GlobalThis => "typeof globalThis".to_string(),
            TyKind::StringLiteral(string_literal) => quoted_property_name(
                string_literal.value,
                flags.contains(TypeFormatFlags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL),
            ),
            TyKind::NumberLiteral(number_literal) => {
                // Print the base-10 representation of the number
                if number_literal.value.is_zero() {
                    // Treat +0 and -0 as the same when printing.
                    "0".to_string()
                } else {
                    number_literal.value.to_string()
                }
            }
            TyKind::BooleanLiteral(value) => value.to_string(),
            TyKind::BigIntLiteral(big_int_literal) => format!("{}n", big_int_literal.value),
            TyKind::TemplateLiteral(template_literal) => {
                let mut repr = String::from("`");

                for (index, quasi) in template_literal.quasis.iter().enumerate() {
                    repr.push_str(quasi.value);
                    if let Some(expression) = template_literal.expressions.get(index) {
                        repr.push_str("${");
                        repr.push_str(&self.to_type_string_with_flags(
                            *expression,
                            replace_type_reference,
                            flags,
                            depth,
                        ));
                        repr.push('}');
                    }
                }

                if template_literal.expressions.len() > template_literal.quasis.len() {
                    for expression in template_literal
                        .expressions
                        .iter()
                        .skip(template_literal.quasis.len())
                    {
                        repr.push_str("${");
                        repr.push_str(&self.to_type_string_with_flags(
                            *expression,
                            replace_type_reference,
                            flags,
                            depth,
                        ));
                        repr.push('}');
                    }
                }

                repr.push('`');
                repr
            }
            TyKind::Array(array) => {
                let element_type = self.to_type_string_with_flags(
                    array.element_type,
                    replace_type_reference,
                    flags,
                    depth,
                );
                if array.display_as_generic
                    && flags.contains(TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE)
                {
                    let name = if array.readonly {
                        "ReadonlyArray"
                    } else {
                        "Array"
                    };
                    return format!("{name}<{element_type}>");
                }
                let body = if self.display_needs_parentheses(array.element_type) {
                    format!("({element_type})[]")
                } else {
                    format!("{element_type}[]")
                };
                if array.readonly {
                    format!("readonly {body}")
                } else {
                    body
                }
            }
            TyKind::Tuple(tuple) => {
                let elements = tuple
                    .elements
                    .iter()
                    .enumerate()
                    .map(|(index, element)| {
                        let label = tuple.labels().and_then(|labels| labels[index]);
                        match (label, element) {
                            (Some(label), TupleElement::Regular(ty)) => format!(
                                "{label}: {}",
                                self.to_type_string_with_flags(
                                    *ty,
                                    replace_type_reference,
                                    flags,
                                    depth,
                                )
                            ),
                            (Some(label), TupleElement::Rest(ty)) => format!(
                                "...{label}: {}",
                                self.to_type_string_with_flags(
                                    *ty,
                                    replace_type_reference,
                                    flags,
                                    depth,
                                )
                            ),
                            (Some(label), TupleElement::Optional(ty)) => format!(
                                "{label}?: {}",
                                self.to_type_string_with_flags(
                                    *ty,
                                    replace_type_reference,
                                    flags,
                                    depth,
                                )
                            ),
                            (None, TupleElement::Regular(ty)) => self.to_type_string_with_flags(
                                *ty,
                                replace_type_reference,
                                flags,
                                depth,
                            ),
                            (None, TupleElement::Rest(ty)) => format!(
                                "...{}",
                                self.to_type_string_with_flags(
                                    *ty,
                                    replace_type_reference,
                                    flags,
                                    depth,
                                )
                            ),
                            (None, TupleElement::Optional(ty)) => {
                                let type_string = self.to_type_string_with_flags(
                                    *ty,
                                    replace_type_reference,
                                    flags,
                                    depth,
                                );
                                if self.element_type_needs_parentheses(element) {
                                    format!("({type_string})?")
                                } else {
                                    format!("{type_string}?")
                                }
                            }
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                if tuple.readonly {
                    format!("readonly [{elements}]")
                } else {
                    format!("[{elements}]")
                }
            }
            TyKind::Union(union) => union
                .types
                .iter()
                .map(|ty| {
                    let type_string =
                        self.to_type_string_with_flags(*ty, replace_type_reference, flags, depth);
                    if self.display_needs_parentheses(*ty) {
                        format!("({type_string})")
                    } else {
                        type_string
                    }
                })
                .collect::<Vec<_>>()
                .join(" | "),
            TyKind::Intersection(intersection) => intersection
                .types
                .iter()
                .map(|ty| {
                    let type_string =
                        self.to_type_string_with_flags(*ty, replace_type_reference, flags, depth);
                    if self.display_needs_parentheses(*ty) {
                        format!("({type_string})")
                    } else {
                        type_string
                    }
                })
                .collect::<Vec<_>>()
                .join(" & "),
            TyKind::Keyof(keyof) => {
                let target = self.to_type_string_with_flags(
                    keyof.target,
                    replace_type_reference,
                    flags,
                    depth,
                );
                if self.display_needs_parentheses(keyof.target) {
                    format!("keyof ({target})")
                } else {
                    format!("keyof {target}")
                }
            }
            TyKind::IndexedAccess(indexed_access) => {
                let object_type = self.to_type_string_with_flags(
                    indexed_access.object_type,
                    replace_type_reference,
                    flags,
                    depth,
                );
                let index_type = self.to_type_string_with_flags(
                    indexed_access.index_type,
                    replace_type_reference,
                    flags,
                    depth,
                );
                if self.display_needs_parentheses(indexed_access.object_type) {
                    format!("({object_type})[{index_type}]")
                } else {
                    format!("{object_type}[{index_type}]")
                }
            }
            TyKind::Conditional(conditional) => {
                let check_type = self.to_type_string_with_flags(
                    conditional.check_type,
                    replace_type_reference,
                    flags,
                    depth,
                );
                let extends_type = self.to_type_string_with_flags(
                    conditional.extends_type,
                    replace_type_reference,
                    flags
                        | if conditional.extends_type.is_function(arena) {
                            TypeFormatFlags::PARENTHESIZE_CONDITIONAL_RETURN
                        } else {
                            TypeFormatFlags::NONE
                        },
                    depth,
                );
                let check_type = if self.display_needs_parentheses(conditional.check_type) {
                    format!("({check_type})")
                } else {
                    check_type
                };
                let extends_type = if matches!(
                    self.checker.ty_kind(conditional.extends_type),
                    TyKind::Conditional(_)
                ) {
                    format!("({extends_type})")
                } else {
                    extends_type
                };
                format!(
                    "{check_type} extends {extends_type} ? {} : {}",
                    self.to_type_string_with_flags(
                        conditional.true_type,
                        replace_type_reference,
                        flags,
                        depth,
                    ),
                    self.to_type_string_with_flags(
                        conditional.false_type,
                        replace_type_reference,
                        flags,
                        depth,
                    )
                )
            }
            TyKind::Infer(infer) => format!(
                "infer {}",
                self.type_parameter_to_type_string(&infer.type_parameter, &|_| None, flags, depth,)
            ),
            TyKind::Mapped(mapped) => {
                let mut string = String::from("{ ");
                let prefix = match mapped.readonly {
                    MappedModifier::None => "",
                    MappedModifier::True => "readonly ",
                    MappedModifier::Plus => "+readonly ",
                    MappedModifier::Minus => "-readonly ",
                };
                string.push_str(prefix);
                string.push('[');
                string.push_str(mapped.key);
                string.push_str(" in ");
                string.push_str(&self.to_type_string_with_flags(
                    mapped.constraint,
                    replace_type_reference,
                    flags,
                    depth,
                ));
                if let Some(name_type) = mapped.name_type {
                    string.push_str(" as ");
                    string.push_str(&self.to_type_string_with_flags(
                        name_type,
                        replace_type_reference,
                        flags,
                        depth,
                    ));
                }
                string.push(']');
                let suffix = match mapped.optional {
                    MappedModifier::None => "",
                    MappedModifier::True => "?",
                    MappedModifier::Plus => "+?",
                    MappedModifier::Minus => "-?",
                };
                string.push_str(suffix);
                string.push_str(": ");
                string.push_str(&self.to_type_string_with_flags(
                    mapped.template,
                    replace_type_reference,
                    flags,
                    depth,
                ));
                string.push_str("; }");
                string
            }
        }
    }

    fn display_needs_parentheses(&self, ty: Ty<'a>) -> bool {
        matches!(
            self.checker.ty_kind(ty),
            TyKind::Function(_)
                | TyKind::Union(_)
                | TyKind::Intersection(_)
                | TyKind::Conditional(_)
                | TyKind::Infer(_)
        ) || matches!(self.checker.ty_kind(ty), TyKind::Object(object) if object.is_constructor_type)
    }

    fn element_type_needs_parentheses(&self, element: &TupleElement<'a>) -> bool {
        self.display_needs_parentheses(element.ty())
    }

    fn type_parameter_to_type_string(
        &self,
        type_parameter: &TyTypeParameter<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let mut type_string = type_parameter.name.to_string();
        if let Some(constraint_type) = type_parameter.constraint_type {
            type_string.push_str(" extends ");
            type_string.push_str(&self.to_type_string_with_flags(
                constraint_type,
                replace_type_reference,
                flags,
                depth,
            ));
        }
        if type_parameter.display_default
            && let Some(default_type) = type_parameter.default_type
        {
            type_string.push_str(" = ");
            type_string.push_str(&self.to_type_string_with_flags(
                default_type,
                replace_type_reference,
                flags,
                depth,
            ));
        }
        type_string
    }

    fn function_type_to_string(
        &self,
        function: &TyFunction<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let (type_parameters, parameters) =
            self.function_type_head_to_string(function, replace_type_reference, flags, depth);
        format!(
            "{type_parameters}({parameters}) => {}",
            self.function_return_type_to_string(function, replace_type_reference, flags, depth)
        )
    }

    fn constructor_type_to_string(
        &self,
        signature: Signature<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let function = signature.function(self.checker.arena());
        let (type_parameters, parameters) =
            self.function_type_head_to_string(function, replace_type_reference, flags, depth);
        let prefix = if signature.is_abstract {
            "abstract new"
        } else {
            "new"
        };
        format!(
            "{prefix} {type_parameters}({parameters}) => {}",
            self.function_return_type_to_string(function, replace_type_reference, flags, depth)
        )
    }

    fn signature_to_type_string(
        &self,
        signature: Signature<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let function = signature.function(self.checker.arena());
        match signature.kind {
            SignatureKind::Call => format!(
                "{};",
                self.signature_to_type_string_for_function(
                    function,
                    replace_type_reference,
                    flags,
                    depth,
                )
            ),
            SignatureKind::Construct => format!(
                "new {};",
                self.signature_to_type_string_for_function(
                    function,
                    replace_type_reference,
                    flags,
                    depth,
                )
            ),
        }
    }

    fn signature_to_type_string_for_function(
        &self,
        function: &TyFunction<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let (type_parameters, parameters) =
            self.function_type_head_to_string(function, replace_type_reference, flags, depth);
        format!(
            "{type_parameters}({parameters}): {}",
            self.function_return_type_to_string(function, replace_type_reference, flags, depth)
        )
    }

    fn function_return_type_to_string(
        &self,
        function: &TyFunction<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let return_type = function.type_predicate.map_or_else(
            || {
                self.to_type_string_with_flags(
                    function.return_type,
                    replace_type_reference,
                    flags | TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE,
                    depth,
                )
            },
            |predicate| {
                self.type_predicate_to_type_string(predicate, replace_type_reference, flags, depth)
            },
        );
        if flags.contains(TypeFormatFlags::PARENTHESIZE_CONDITIONAL_RETURN)
            && function.type_predicate.is_none()
            && matches!(
                self.checker.ty_kind(function.return_type),
                TyKind::Conditional(_)
            )
        {
            format!("({return_type})")
        } else {
            return_type
        }
    }

    fn type_predicate_to_type_string(
        &self,
        predicate: &TyTypePredicate<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> String {
        let (prefix, parameter_name, target_type) = match *predicate {
            TyTypePredicate::This { target_type } => ("", "this", Some(target_type)),
            TyTypePredicate::Identifier {
                parameter_name,
                target_type,
                ..
            } => ("", parameter_name, Some(target_type)),
            TyTypePredicate::AssertsThis { target_type } => ("asserts ", "this", target_type),
            TyTypePredicate::AssertsIdentifier {
                parameter_name,
                target_type,
                ..
            } => ("asserts ", parameter_name, target_type),
        };
        let mut type_string = format!("{prefix}{parameter_name}");
        if let Some(target_type) = target_type {
            type_string.push_str(" is ");
            type_string.push_str(&self.to_type_string_with_flags(
                target_type,
                replace_type_reference,
                flags,
                depth,
            ));
        }
        type_string
    }

    fn function_type_head_to_string(
        &self,
        function: &TyFunction<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> (String, String) {
        let type_parameters = if function.type_parameters.is_empty() {
            String::new()
        } else {
            let type_parameters = function
                .type_parameters
                .iter()
                .map(|type_parameter| {
                    if function.display_type_parameters_as_arguments {
                        type_parameter.name.to_string()
                    } else {
                        self.type_parameter_to_type_string(
                            type_parameter,
                            replace_type_reference,
                            flags,
                            depth,
                        )
                    }
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("<{type_parameters}>")
        };
        let parameters = function
            .parameters
            .iter()
            .flat_map(|parameter| {
                self.function_parameter_to_type_strings(
                    parameter,
                    replace_type_reference,
                    flags | TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE,
                    depth,
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        (type_parameters, parameters)
    }

    fn function_parameter_to_type_strings(
        &self,
        parameter: &TyParameter<'a>,
        replace_type_reference: &dyn Fn(Ty<'a>) -> Option<Ty<'a>>,
        flags: TypeFormatFlags,
        depth: &Cell<usize>,
    ) -> Vec<String> {
        if parameter.rest
            && let TyKind::Tuple(tuple) = self.checker.ty_kind(parameter.ty)
            && !tuple
                .elements
                .iter()
                .any(|element| matches!(element, TupleElement::Rest(_)))
        {
            return tuple
                .elements
                .iter()
                .enumerate()
                .map(|(index, element)| {
                    let name = format!("{}_{}", parameter.name, index);
                    match element {
                        TupleElement::Regular(ty) => format!(
                            "{name}: {}",
                            self.to_type_string_with_flags(
                                *ty,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        ),
                        TupleElement::Optional(ty) => format!(
                            "{name}?: {}",
                            self.to_type_string_with_flags(
                                *ty,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        ),
                        TupleElement::Rest(ty) => format!(
                            "...{name}: {}",
                            self.to_type_string_with_flags(
                                *ty,
                                replace_type_reference,
                                flags,
                                depth,
                            )
                        ),
                    }
                })
                .collect();
        }

        if parameter.rest {
            vec![format!(
                "...{}: {}",
                parameter.name,
                self.to_type_string_with_flags(parameter.ty, replace_type_reference, flags, depth,)
            )]
        } else if parameter.optional {
            vec![format!(
                "{}?: {}",
                parameter.name,
                self.to_type_string_with_flags(parameter.ty, replace_type_reference, flags, depth,)
            )]
        } else {
            vec![format!(
                "{}: {}",
                parameter.name,
                self.to_type_string_with_flags(parameter.ty, replace_type_reference, flags, depth,)
            )]
        }
    }
}

impl<'a> Checker<'a, '_> {
    /// Returns the display string for a type using this checker's arena.
    ///
    /// This form does not use source-location-specific type-alias expansion.
    /// Use [`Checker::type_to_string`] when the source location is available.
    ///
    /// # Example
    ///
    /// ```
    /// use oxc_allocator::Allocator;
    /// use oxc_checker::{
    ///     Ty,
    ///     checker::Checker,
    ///     program::{FsProgramHost, ProgramStoreBuilder},
    /// };
    ///
    /// let allocator = Allocator::default();
    /// let store = ProgramStoreBuilder::new(&allocator, FsProgramHost::new())
    ///     .without_default_lib()
    ///     .build()
    ///     .unwrap();
    /// let checker = Checker::new(&store);
    /// assert_eq!(checker.to_type_string(Ty::string()), "string");
    /// ```
    pub fn to_type_string(&self, ty: Ty<'a>) -> String {
        TypePrinter::new(self).to_type_string(ty)
    }
}

fn property_name_to_type_string(
    property: &TyProperty<'_>,
    format_flags: TypeFormatFlags,
) -> String {
    let name = if property.computed {
        format!("[{}]", property.name)
    } else if is_identifier_name(property.name) || is_numeric_property_name(property.name) {
        property.name.to_string()
    } else {
        quoted_property_name(
            property.name,
            format_flags.contains(TypeFormatFlags::PRESERVE_PROPERTY_NAME_QUOTES)
                && property.flags.contains(TyPropertyFlags::SINGLE_QUOTED),
        )
    };
    if property.optional {
        format!("{name}?")
    } else {
        name
    }
}

fn quoted_property_name(name: &str, single_quoted: bool) -> String {
    let mut quoted = String::with_capacity(name.len() + 2);
    let delimiter = if single_quoted { '\'' } else { '"' };
    quoted.push(delimiter);
    for character in name.chars() {
        match character {
            '\\' => quoted.push_str("\\\\"),
            '\n' => quoted.push_str("\\n"),
            '\r' => quoted.push_str("\\r"),
            '\t' => quoted.push_str("\\t"),
            _ if character == delimiter => {
                quoted.push('\\');
                quoted.push(character);
            }
            _ => quoted.push(character),
        }
    }
    quoted.push(delimiter);
    quoted
}

fn is_numeric_property_name(name: &str) -> bool {
    name.parse::<f64>().is_ok()
        || name
            .strip_prefix("0x")
            .or_else(|| name.strip_prefix("0X"))
            .is_some_and(|digits| {
                !digits.is_empty()
                    && digits
                        .chars()
                        .all(|character| character.is_ascii_hexdigit())
            })
        || name
            .strip_prefix("0b")
            .or_else(|| name.strip_prefix("0B"))
            .is_some_and(|digits| {
                !digits.is_empty()
                    && digits
                        .chars()
                        .all(|character| matches!(character, '0' | '1'))
            })
        || name
            .strip_prefix("0o")
            .or_else(|| name.strip_prefix("0O"))
            .is_some_and(|digits| {
                !digits.is_empty()
                    && digits
                        .chars()
                        .all(|character| matches!(character, '0'..='7'))
            })
}
