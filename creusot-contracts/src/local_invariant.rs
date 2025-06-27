use crate::*;

/// Declare a new namespace.
///
/// # Example
///
/// ```rust
/// use creusot_contracts::{*, local_invariant::{declare_namespace, Namespace}, logic::Set};
/// declare_namespace! { A }
///
/// #[requires(ns.contains(A()))]
/// fn foo(ns: Ghost<&mut Set<Namespace>>) { /* ... */ }
/// ```
pub use base_macros::declare_namespace;

/// The type of _namespaces_ associated with invariants.
///
/// FIXME: more docs
#[cfg_attr(creusot, rustc_diagnostic_item = "namespace_ty")]
pub struct Namespace(());

impl Namespace {
    /// Used by [`declare_namespace`].
    #[logic]
    #[open(self)]
    #[requires(false)]
    #[doc(hidden)]
    pub fn new() -> Self {
        Self(())
    }
}
