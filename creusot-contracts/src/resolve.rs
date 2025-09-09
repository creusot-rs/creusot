//! Resolve mutable borrows
pub use crate::base_macros::Resolve;
use crate::*;

pub trait Resolve {
    #[logic(prophetic)]
    #[rustc_diagnostic_item = "creusot_resolve_method"]
    fn resolve(self) -> bool;

    #[logic(prophetic)]
    #[requires(inv(self))]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self);
}

#[trusted]
#[logic(prophetic)]
#[open]
#[rustc_diagnostic_item = "creusot_resolve"]
pub fn resolve<T: ?Sized>(_: T) -> bool {
    dead
}

#[trusted]
#[logic(prophetic)]
#[open]
#[rustc_diagnostic_item = "creusot_structural_resolve"]
pub fn structural_resolve<T: ?Sized>(_: T) -> bool {
    dead
}

impl<T1, T2: ?Sized> Resolve for (T1, T2) {
    #[open]
    #[logic(prophetic)]
    #[creusot::why3_meta("rewrite_def", predicate, self)]
    fn resolve(self) -> bool {
        resolve(self.0) && resolve(self.1)
    }

    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<T: ?Sized> Resolve for &mut T {
    #[open]
    #[logic(prophetic)]
    #[creusot::why3_meta("rewrite_def", predicate, self)]
    fn resolve(self) -> bool {
        pearlite! { ^self == *self }
    }

    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<T: ?Sized> Resolve for Box<T> {
    #[open]
    #[logic(prophetic)]
    #[creusot::why3_meta("rewrite_def", predicate, self)]
    fn resolve(self) -> bool {
        resolve(*self)
    }

    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}
