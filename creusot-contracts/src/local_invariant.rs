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
#[trusted] // This type has a very special translation.
pub struct Namespace(());
