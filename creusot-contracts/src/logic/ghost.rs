use crate as creusot_contracts;
use crate::logic::*;
use creusot_contracts_proc::*;

#[rustc_diagnostic_item = "creusot_ghost"]
pub struct Ghost<T>(*mut T)
where
    T: ?Sized;

impl<T> Model for Ghost<T> {
    type ModelTy = T;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        absurd
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
    pub fn inner(self) -> T {
        pearlite! { absurd }
    }
}
