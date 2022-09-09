use crate as creusot_contracts;
use crate::macros::*;
use core::ops::Deref;

pub struct Ghost<T>(pub T)
where
    T: ?Sized;

impl<T> Deref for Ghost<T> {
    type Target = T;

    #[logic]
    #[trusted]
    // #[creusot::builtins = "ghost_deref"]
    #[ensures(*result == self.0)]
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
    pub fn unwrap(self) -> T {
        self.0
    }

    #[logic]
    pub fn inner(&self) -> T {
        self.0
    }
}
