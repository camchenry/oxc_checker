use std::cell::{Cell, RefCell};

/// Maximum recursion depth for expanding aliases, mapped types, indexed access,
/// and apparent types at use sites before preserving the current unresolved type.
pub(crate) const TYPE_EXPANSION_MAX_DEPTH: usize = 32;

/// Maximum recursion depth for substituting type parameters through nested type
/// structures before returning the partially instantiated type unchanged.
pub(crate) const TYPE_INSTANTIATION_MAX_DEPTH: usize = 64;

/// Maximum recursion depth for resolving TypeScript AST type nodes into checker
/// types before falling back to `any` for pathological recursive annotations.
pub(crate) const TS_TYPE_RESOLUTION_MAX_DEPTH: usize = 128;

/// Maximum recursion depth for matching `infer` placeholders inside conditional
/// type `extends` patterns before deferring the match.
pub(crate) const CONDITIONAL_INFER_MATCH_MAX_DEPTH: usize = 64;

/// Maximum recursion depth for resolving conditional types before preserving the
/// conditional type as deferred instead of selecting a branch.
pub(crate) const CONDITIONAL_TYPE_MAX_DEPTH: usize = 64;

/// Maximum recursion depth for structural assignability checks before treating
/// the relation as not assignable.
pub(crate) const ASSIGNABILITY_MAX_DEPTH: usize = 128;

/// Maximum recursion depth for rendering type strings before using a compact
/// fallback representation.
pub(crate) const TYPE_STRING_MAX_DEPTH: usize = 64;

/// Maximum recursion depth for generic type traversal helpers before stopping
/// traversal of the current branch.
pub(crate) const TYPE_VISIT_MAX_DEPTH: usize = 256;

/// Key used to identify an active interface property lookup and break recursive
/// interface property resolution cycles.
pub(crate) type InterfacePropertyResolutionKey = (usize, String, String);

thread_local! {
    /// Per-thread recursion depth for TypeScript AST type-node resolution.
    pub(crate) static TS_TYPE_RESOLUTION_DEPTH: Cell<usize> = const { Cell::new(0) };

    /// Per-thread stack of active interface property lookups used as a cycle guard.
    pub(crate) static INTERFACE_PROPERTY_RESOLUTION_STACK: RefCell<Vec<InterfacePropertyResolutionKey>> = const { RefCell::new(Vec::new()) };

    /// Per-thread recursion depth for conditional type resolution.
    pub(crate) static CONDITIONAL_TYPE_DEPTH: Cell<usize> = const { Cell::new(0) };

    /// Per-thread recursion depth for type string rendering.
    pub(crate) static TYPE_STRING_DEPTH: Cell<usize> = const { Cell::new(0) };
}
