use crate as creusot_contracts;
use crate::macros::*;
use core::ops::Deref;

#[rustc_diagnostic_item = "ghost_type"]
pub struct Ghost<T>(pub T)
where
    T: ?Sized;

impl<T> Deref for Ghost<T> {
    type Target = T;

    #[logic]
    #[trusted]
    #[creusot::builtins = "ghost_deref"]
    fn deref(&self) -> &Self::Target {
        absurd
    }
}

impl<T> Ghost<T> {
    #[logic]
    pub fn new(a: &T) -> Ghost<T> {
        Ghost(*a)
    }

    #[logic]
    #[creusot::builtins = "ghost_inner"]
    pub fn unwrap(self) -> T {
        self.0
    }

    #[logic]
    pub fn inner(&self) -> T {
        self.0
    }
}
