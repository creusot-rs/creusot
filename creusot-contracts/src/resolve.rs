//! Resolve mutable borrows
use crate::*;

/// This logical function is assumed as soon as a value leaves its scope. It states that the
/// propheties of every mutable borrow appearing in it parameter is eaqual to its current value.
///
/// Its body is opaque, but Creusot automatically generates an axiom stating relevant properties
/// depending on the definition of `T`.
#[logic(prophetic, inline, open)]
#[intrinsic("resolve")]
pub fn resolve<T: ?Sized>(_: T) -> bool {
    dead
}

/// The trait `Resolve` makes it possible to expose to clients a custom resolve assertion for
/// opaque types.
///
/// For example, if a library defines a notion of finite mapping, it does not exposes the internal
/// representation of the finite mapping data structure. Hence, the `resolve` predicate above wil be
/// completely opaque for clients. This library should implement the `Resolve` trait in order to
/// provide to the client a definition it can use. E.g., `Resolve::resolve` states that any element
/// of the mapping is resolved.
pub trait Resolve {
    #[logic(prophetic)]
    #[intrinsic("resolve_method")]
    fn resolve(self) -> bool;

    #[logic(prophetic)]
    #[requires(inv(self))]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self);
}

#[logic(open, prophetic)]
#[intrinsic("structural_resolve")]
pub fn structural_resolve<T: ?Sized>(_: T) -> bool {
    dead
}

// Instances for fundamental types, which make impossible

impl<'a, T: ?Sized> Resolve for &'a T {
    #[logic(open)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn resolve(self) -> bool {
        true
    }

    #[logic]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<'a, T: ?Sized> Resolve for &'a mut T {
    #[logic(open)]
    fn resolve(self) -> bool {
        true
    }

    #[logic]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}
