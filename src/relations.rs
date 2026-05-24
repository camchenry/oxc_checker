use crate::types::Ty;

pub(crate) fn is_assignable_to<'a>(source: Ty<'a>, target: Ty<'a>) -> bool {
    if source == target {
        return true;
    }

    match (source, target) {
        (_, Ty::Any | Ty::Unknown) | (Ty::Any, _) => true,
        (Ty::Object(source), Ty::Object(target)) => {
            target.properties.iter().all(|target_property| {
                source
                    .properties
                    .iter()
                    .find(|source_property| source_property.name == target_property.name)
                    .is_some_and(|source_property| {
                        is_assignable_to(source_property.ty, target_property.ty)
                    })
            })
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
        (Ty::Type(source), Ty::Type(target)) => source.name == target.name,
        _ => false,
    }
}
