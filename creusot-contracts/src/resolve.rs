use crate::*;
pub use crate::{base_macros::Resolve, invariant::*};

pub trait Resolve {
    #[predicate(prophetic)]
    #[rustc_diagnostic_item = "creusot_resolve_method"]
    fn resolve(self) -> bool;

    #[logic(prophetic)]
    #[requires(inv(self))]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self);
}

#[predicate(prophetic)]
#[open]
#[rustc_diagnostic_item = "creusot_resolve"]
pub fn resolve<T: ?Sized>(_: &T) -> bool {
    true
}

impl<T1, T2: ?Sized> Resolve for (T1, T2) {
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        resolve(&self.0) && resolve(&self.1)
    }

    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<T: ?Sized> Resolve for &mut T {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! { ^self == *self }
    }

    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<T: ?Sized> Resolve for Box<T> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        resolve(&*self)
    }

    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<T> Resolve for Option<T> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        match self {
            Some(x) => resolve(&x),
            None => true,
        }
    }

    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

#[open(self)]
#[cfg_attr(creusot, predicate(prophetic))]
#[cfg_attr(creusot, creusot::open_inv)]
#[cfg_attr(creusot, creusot::open_inv_result)]
#[cfg_attr(creusot, rustc_diagnostic_item = "creusot_structural_resolve")]
pub fn structural_resolve<T: ?Sized>(_: &T) -> bool {
    true
}
