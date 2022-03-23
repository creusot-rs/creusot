use crate as creusot_contracts;
use creusot_contracts_proc::*;

#[rustc_diagnostic_item = "creusot_resolve"]
pub unsafe trait Resolve {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_resolve_method"]
    fn resolve(self) -> bool;
}

unsafe impl<T1, T2> Resolve for (T1, T2) {
    #[predicate]
    fn resolve(self) -> bool {
        Resolve::resolve(self.0) && Resolve::resolve(self.1)
    }
}

unsafe impl<T: ?Sized> Resolve for &mut T {
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! { ^self === *self }
    }
}

unsafe impl<T> Resolve for T {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_resolve_default"]
    default fn resolve(self) -> bool {
        true
    }
}
