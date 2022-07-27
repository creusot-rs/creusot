use crate as creusot_contracts;
use crate::macros::*;

#[cfg_attr(feature = "contracts", rustc_diagnostic_item = "creusot_resolve")]
#[trusted]
pub trait Resolve {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_resolve_method"]
    fn resolve(self) -> bool;
}

#[trusted]
impl<T1, T2> Resolve for (T1, T2) {
    #[predicate]
    fn resolve(self) -> bool {
        Resolve::resolve(self.0) && Resolve::resolve(self.1)
    }
}

#[trusted]
impl<T: ?Sized> Resolve for &mut T {
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! { ^self == *self }
    }
}

#[cfg(feature = "contracts")]
#[trusted]
impl<T> Resolve for T {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_resolve_default"]
    default fn resolve(self) -> bool {
        true
    }
}
