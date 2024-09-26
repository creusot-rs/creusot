pub use crate::base_macros::Resolve;
use crate::*;

#[trusted]
pub trait Resolve {
    #[predicate(prophetic)]
    #[rustc_diagnostic_item = "creusot_resolve_method"]
    fn resolve(self) -> bool;
}

#[predicate(prophetic)]
#[open]
#[rustc_diagnostic_item = "creusot_resolve"]
pub fn resolve<T: ?Sized>(_: &T) -> bool {
    true
}

#[trusted]
impl<T1, T2: ?Sized> Resolve for (T1, T2) {
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        resolve(&self.0) && resolve(&self.1)
    }
}

#[trusted]
impl<T: ?Sized> Resolve for &mut T {
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        pearlite! { ^self == *self }
    }
}

#[trusted]
impl<T: ?Sized> Resolve for Box<T> {
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        resolve(&*self)
    }
}
