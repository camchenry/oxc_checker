use std::collections::HashMap;

use oxc_ast::ast::{FormalParameters, TSSignature, TSTupleElement, TSType};

use crate::types::Ty;

pub fn infer_type_parameter_from_types<'a>(
    parameter_type: &Ty<'a>,
    argument_type: &Ty<'a>,
    type_parameters: &[&'a str],
    substitutions: &mut HashMap<&'a str, Ty<'a>>,
) {
    match (parameter_type, argument_type) {
        (Ty::Union(parameter_union), _) => {
            infer_type_parameter_from_union(
                parameter_union.types.iter().copied(),
                argument_type,
                type_parameters,
                substitutions,
            );
        }
        (Ty::TypeReference(reference), _)
            if reference.type_arguments.is_empty() && type_parameters.contains(&reference.name) =>
        {
            match substitutions.get(reference.name) {
                Some(existing) if existing != argument_type => {
                    substitutions.insert(reference.name, Ty::any());
                }
                Some(_) => {}
                None => {
                    substitutions.insert(reference.name, *argument_type);
                }
            }
        }
        (Ty::TypeReference(parameter_reference), Ty::TypeReference(argument_reference))
            if parameter_reference.name == argument_reference.name =>
        {
            for (parameter_type, argument_type) in parameter_reference
                .type_arguments
                .iter()
                .zip(argument_reference.type_arguments.iter())
            {
                infer_type_parameter_from_types(
                    parameter_type,
                    argument_type,
                    type_parameters,
                    substitutions,
                );
            }
        }
        (Ty::Object(parameter_object), Ty::Object(argument_object)) => {
            for parameter_property in &parameter_object.properties {
                if let Some(argument_property) =
                    argument_object.properties.iter().find(|argument_property| {
                        argument_property.name == parameter_property.name
                            && argument_property.computed == parameter_property.computed
                    })
                {
                    infer_type_parameter_from_types(
                        &parameter_property.ty,
                        &argument_property.ty,
                        type_parameters,
                        substitutions,
                    );
                }
            }
        }
        (Ty::Function(parameter_function), Ty::Function(argument_function)) => {
            for (parameter, argument) in parameter_function
                .parameters
                .iter()
                .zip(argument_function.parameters.iter())
            {
                infer_type_parameter_from_types(
                    &parameter.ty,
                    &argument.ty,
                    type_parameters,
                    substitutions,
                );
            }
            infer_type_parameter_from_types(
                &parameter_function.return_type,
                &argument_function.return_type,
                type_parameters,
                substitutions,
            );
        }
        _ => {}
    }
}

fn infer_type_parameter_from_union<'a>(
    parameter_types: impl IntoIterator<Item = Ty<'a>>,
    argument_type: &Ty<'a>,
    type_parameters: &[&'a str],
    substitutions: &mut HashMap<&'a str, Ty<'a>>,
) {
    let parameter_types = parameter_types
        .into_iter()
        .filter(|ty| !matches!(ty, Ty::Null | Ty::Undefined | Ty::Never))
        .collect::<Vec<_>>();

    let candidates = match argument_type {
        Ty::Function(_) => parameter_types
            .iter()
            .copied()
            .filter(|ty| matches!(ty, Ty::Function(_)))
            .collect::<Vec<_>>(),
        Ty::TypeReference(argument_reference) => parameter_types
            .iter()
            .copied()
            .filter(|ty| {
                matches!(ty, Ty::TypeReference(parameter_reference) if parameter_reference.name == argument_reference.name)
            })
            .collect::<Vec<_>>(),
        _ => Vec::new(),
    };

    let candidates = if candidates.is_empty() {
        parameter_types
            .iter()
            .copied()
            .filter(|ty| {
                matches!(ty, Ty::TypeReference(reference) if reference.type_arguments.is_empty() && type_parameters.contains(&reference.name))
            })
            .collect::<Vec<_>>()
    } else {
        candidates
    };

    let candidates = if candidates.is_empty() {
        parameter_types
    } else {
        candidates
    };

    for candidate in candidates {
        infer_type_parameter_from_types(&candidate, argument_type, type_parameters, substitutions);
    }
}

pub fn ts_signature_contains_infer(signature: &TSSignature<'_>) -> bool {
    match signature {
        TSSignature::TSPropertySignature(property) => property
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation)),
        TSSignature::TSMethodSignature(method) => {
            formal_parameters_contain_infer(method.params.as_ref())
                || method
                    .return_type
                    .as_deref()
                    .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
        }
        TSSignature::TSCallSignatureDeclaration(signature) => {
            formal_parameters_contain_infer(signature.params.as_ref())
                || signature
                    .return_type
                    .as_deref()
                    .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
        }
        TSSignature::TSConstructSignatureDeclaration(signature) => {
            formal_parameters_contain_infer(signature.params.as_ref())
                || signature
                    .return_type
                    .as_deref()
                    .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
        }
        _ => false,
    }
}

pub fn formal_parameters_contain_infer(parameters: &FormalParameters<'_>) -> bool {
    parameters.items.iter().any(|parameter| {
        parameter
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
    }) || parameters.rest.as_ref().is_some_and(|parameter| {
        parameter
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation))
    })
}

pub fn ts_type_contains_infer(ty: &TSType<'_>) -> bool {
    match ty {
        TSType::TSInferType(_) => true,
        TSType::TSArrayType(array) => ts_type_contains_infer(&array.element_type),
        TSType::TSTupleType(tuple) => tuple.element_types.iter().any(|element| match element {
            TSTupleElement::TSRestType(rest) => ts_type_contains_infer(&rest.type_annotation),
            TSTupleElement::TSOptionalType(optional) => {
                ts_type_contains_infer(&optional.type_annotation)
            }
            _ => element.as_ts_type().is_some_and(ts_type_contains_infer),
        }),
        TSType::TSUnionType(union) => union.types.iter().any(|ty| ts_type_contains_infer(ty)),
        TSType::TSIntersectionType(intersection) => intersection
            .types
            .iter()
            .any(|ty| ts_type_contains_infer(ty)),
        TSType::TSParenthesizedType(parenthesized) => {
            ts_type_contains_infer(&parenthesized.type_annotation)
        }
        TSType::TSTypeOperatorType(operator) => ts_type_contains_infer(&operator.type_annotation),
        TSType::TSIndexedAccessType(indexed_access) => {
            ts_type_contains_infer(&indexed_access.object_type)
                || ts_type_contains_infer(&indexed_access.index_type)
        }
        TSType::TSConditionalType(conditional) => {
            ts_type_contains_infer(&conditional.check_type)
                || ts_type_contains_infer(&conditional.extends_type)
                || ts_type_contains_infer(&conditional.true_type)
                || ts_type_contains_infer(&conditional.false_type)
        }
        TSType::TSTypeReference(reference) => {
            reference
                .type_arguments
                .as_ref()
                .is_some_and(|type_arguments| {
                    type_arguments
                        .params
                        .iter()
                        .any(|ty| ts_type_contains_infer(ty))
                })
        }
        TSType::TSFunctionType(function) => {
            formal_parameters_contain_infer(function.params.as_ref())
                || ts_type_contains_infer(&function.return_type.type_annotation)
        }
        TSType::TSTypeLiteral(type_literal) => {
            type_literal.members.iter().any(ts_signature_contains_infer)
        }
        TSType::TSMappedType(mapped) => {
            ts_type_contains_infer(&mapped.constraint)
                || mapped
                    .name_type
                    .as_ref()
                    .is_some_and(|ty| ts_type_contains_infer(ty))
                || mapped
                    .type_annotation
                    .as_ref()
                    .is_some_and(|ty| ts_type_contains_infer(ty))
        }
        TSType::TSTypePredicate(predicate) => predicate
            .type_annotation
            .as_deref()
            .is_some_and(|annotation| ts_type_contains_infer(&annotation.type_annotation)),
        _ => false,
    }
}
