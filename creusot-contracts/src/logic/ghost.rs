use crate as creusot_contracts;
use core::ops::Deref;
use creusot_contracts_proc::*;

#[rustc_diagnostic_item = "creusot_ghost"]
pub struct Ghost<T>(*mut T)
where
    T: ?Sized;

impl<T: ?Sized> Deref for Ghost<T> {
    type Target = T;

    #[logic]
    #[trusted]
    #[creusot::builtins = "ghost_deref"]
    fn deref(&self) -> &Self::Target {
        pearlite! { absurd }
    }
}

impl<T> Ghost<T> {
    #[trusted]
    #[logic]
    #[creusot::builtins = "ghost_new"]
    pub fn new(_: &T) -> Ghost<T> {
        pearlite! { absurd }
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "ghost_inner"]
    pub fn inner(&self) -> T {
        pearlite! { absurd }
    }
}
