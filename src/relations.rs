use crate::types::Ty;

pub(crate) fn is_assignable_to<'a>(source: Ty<'a>, target: Ty<'a>) -> bool {
    if source == target {
        return true;
    }

    match (source, target) {
        (_, Ty::Any | Ty::Unknown) | (Ty::Any, _) => true,
        (Ty::Object(source), Ty::Object(target)) => {
            properties_assignable_to(&source.properties, &target.properties)
        }
        (Ty::ModuleNamespace(source), Ty::Object(target)) => {
            properties_assignable_to(&source.properties, &target.properties)
        }
        (Ty::Object(source), Ty::ModuleNamespace(target)) => {
            properties_assignable_to(&source.properties, &target.properties)
        }
        (Ty::ModuleNamespace(source), Ty::ModuleNamespace(target)) => {
            properties_assignable_to(&source.properties, &target.properties)
        }
        (Ty::Function(source), Ty::Function(target)) => {
            source.parameters.len() == target.parameters.len()
                && source.parameters.iter().zip(target.parameters.iter()).all(
                    |(source_parameter, target_parameter)| {
                        is_assignable_to(target_parameter.ty, source_parameter.ty)
                    },
                )
                && is_assignable_to(source.return_type, target.return_type)
        }
        (Ty::TypeReference(source), Ty::TypeReference(target)) => {
            source.name == target.name
                && source.type_arguments.len() == target.type_arguments.len()
                && source
                    .type_arguments
                    .iter()
                    .zip(target.type_arguments.iter())
                    .all(|(source_argument, target_argument)| {
                        is_assignable_to(*source_argument, *target_argument)
                    })
        }
        (Ty::TypeQuery(source), Ty::TypeQuery(target)) => {
            source.name == target.name
                && source.type_arguments.len() == target.type_arguments.len()
                && source
                    .type_arguments
                    .iter()
                    .zip(target.type_arguments.iter())
                    .all(|(source_argument, target_argument)| {
                        is_assignable_to(*source_argument, *target_argument)
                    })
        }
        // A `typeof X` query is transparently compatible with whatever the queried symbol's type allows.
        (Ty::TypeQuery(source), _) => is_assignable_to(source.resolved, target),
        (_, Ty::TypeQuery(target)) => is_assignable_to(source, target.resolved),
        (Ty::Array(source), Ty::Array(target)) => {
            is_assignable_to(source.element_type, target.element_type)
        }
        (Ty::UniqueSymbol(_), Ty::Symbol) => true,
        (Ty::NumberLiteral(_), Ty::Number) => true,
        (Ty::StringLiteral(_), Ty::String) => true,
        (Ty::BooleanLiteral(_), Ty::Boolean) => true,
        _ => false,
    }
}

fn properties_assignable_to<'a>(
    source_properties: &[crate::types::TyProperty<'a>],
    target_properties: &[crate::types::TyProperty<'a>],
) -> bool {
    target_properties.iter().all(|target_property| {
        let Some(source_property) = source_properties.iter().find(|source_property| {
            source_property.name == target_property.name
                && source_property.computed == target_property.computed
        }) else {
            return target_property.optional;
        };

        if source_property.optional
            && !target_property.optional
            && !is_assignable_to(Ty::undefined(), target_property.ty)
        {
            return false;
        }

        is_assignable_to(source_property.ty, target_property.ty)
    })
}
