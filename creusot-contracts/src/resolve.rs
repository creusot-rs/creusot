use crate::*;

#[cfg_attr(creusot, rustc_diagnostic_item = "creusot_resolve")]
#[trusted]
pub trait Resolve {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_resolve_method"]
    fn resolve(self) -> bool;
}

#[trusted]
impl<T1, T2> Resolve for (T1, T2) {
    #[predicate]
    #[open]
    fn resolve(self) -> bool {
        Resolve::resolve(self.0) && Resolve::resolve(self.1)
    }
}

#[trusted]
impl<T: ?Sized> Resolve for &mut T {
    #[predicate]
    #[open]
    fn resolve(self) -> bool {
        pearlite! { ^self == *self }
    }
}

#[trusted]
impl<T> Resolve for Box<T> {
    #[predicate]
    #[open]
    fn resolve(self) -> bool {
        Resolve::resolve(*self)
    }
}

#[cfg(creusot)]
#[trusted]
impl<T> Resolve for T {
    #[predicate]
    #[open]
    #[rustc_diagnostic_item = "creusot_resolve_default"]
    default fn resolve(self) -> bool {
        true
    }
}
