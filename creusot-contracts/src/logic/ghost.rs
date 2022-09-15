use crate as creusot_contracts;
use crate::macros::*;
use core::ops::Deref;

#[cfg_attr(feature = "contracts", creusot::builtins = "prelude.Ghost.ghost_ty")]
pub struct Ghost<T>(std::marker::PhantomData<T>)
where
    T: ?Sized;

impl<T> Deref for Ghost<T> {
    type Target = T;

    #[trusted]
    #[logic]
    #[creusot::builtins = "prelude.Ghost.inner"]
    fn deref(&self) -> &Self::Target {
        absurd
    }
}

impl<T> Ghost<T> {
    #[trusted]
    #[logic]
    #[creusot::builtins = "prelude.Ghost.new"]
    pub fn new(_: T) -> Ghost<T> {
        pearlite! { absurd }
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "prelude.Ghost.inner"]
    pub fn inner(self) -> T {
        pearlite! { absurd }
    }
}
