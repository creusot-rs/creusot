use crate::*;

#[cfg_attr(creusot, rustc_diagnostic_item = "creusot_resolve")]
#[trusted]
pub trait Resolve {
    #[predicate(prophetic)]
    #[rustc_diagnostic_item = "creusot_resolve_method"]
    fn resolve(self) -> bool;
}

#[trusted]
impl<T1, T2: ?Sized> Resolve for (T1, T2) {
    #[predicate(prophetic)]
    #[open]
    fn resolve(self) -> bool {
        Resolve::resolve(self.0) && Resolve::resolve(self.1)
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
        Resolve::resolve(*self)
    }
}

#[cfg(creusot)]
#[trusted]
impl<T: ?Sized> Resolve for T {
    #[predicate]
    #[open]
    #[rustc_diagnostic_item = "creusot_resolve_default"]
    default fn resolve(self) -> bool {
        true
    }
}
