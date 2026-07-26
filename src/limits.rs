/// Maximum recursion depth for expanding aliases, mapped types, indexed access,
/// and apparent types at use sites before preserving the current unresolved type.
pub(crate) const TYPE_EXPANSION_MAX_DEPTH: usize = 32;

/// Maximum active type instantiation depth before returning `any` for a
/// pathological or infinite generic type, matching TypeScript's limit.
pub(crate) const TYPE_INSTANTIATION_MAX_DEPTH: usize = 100;

/// Maximum recursion depth for resolving TypeScript AST type nodes into checker
/// types before falling back to `any` for pathological recursive annotations.
pub(crate) const TS_TYPE_RESOLUTION_MAX_DEPTH: usize = 128;

/// Maximum recursion depth for matching `infer` placeholders inside conditional
/// type `extends` patterns before deferring the match.
pub(crate) const CONDITIONAL_INFER_MATCH_MAX_DEPTH: usize = 64;

/// Maximum recursion depth for resolving conditional types before preserving the
/// conditional type as deferred instead of selecting a branch.
pub(crate) const CONDITIONAL_TYPE_MAX_DEPTH: usize = 100;

/// Maximum recursion depth for structural assignability checks before treating
/// the relation as not assignable.
pub(crate) const ASSIGNABILITY_MAX_DEPTH: usize = 128;

/// Maximum recursion depth for rendering type strings before using a compact
/// fallback representation.
pub(crate) const TYPE_STRING_MAX_DEPTH: usize = 64;

/// Maximum recursion depth for generic type traversal helpers before stopping
/// traversal of the current branch.
pub(crate) const TYPE_VISIT_MAX_DEPTH: usize = 256;

/// Maximum tuple length produced by spreading tuple types before falling back
/// to `any`, matching TypeScript's tuple normalization limit.
pub(crate) const TUPLE_SPREAD_MAX_LENGTH: usize = 10_000;
