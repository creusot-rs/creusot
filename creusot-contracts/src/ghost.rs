use crate::{std::ops::Deref, *};

#[cfg_attr(creusot, creusot::builtins = "prelude.Ghost.ghost_ty")]
pub struct Ghost<T>(std::marker::PhantomData<T>)
where
    T: ?Sized;

impl<T: ?Sized> Deref for Ghost<T> {
    type Target = T;

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "prelude.Ghost.inner"]
    fn deref(&self) -> &Self::Target {
        pearlite! { absurd }
    }
}

impl<T> ::std::clone::Clone for Ghost<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Ghost<T> {}

impl<T: ShallowModel + ?Sized> ShallowModel for Ghost<T> {
    type ShallowModelTy = T::ShallowModelTy;

    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { self.deref().shallow_model() }
    }
}

impl<T: ?Sized> Ghost<T> {
    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "prelude.Ghost.new"]
    pub fn new(_: T) -> Ghost<T> {
        pearlite! { absurd }
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "prelude.Ghost.from_fn"]
    pub fn from_fn<F: Fn() -> Ghost<T>>(_: F) -> Ghost<T> {
        pearlite! { absurd }
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "prelude.Ghost.inner"]
    #[creusot::prusti::home_sig = "('x) -> 'x"]
    pub fn inner(self) -> T
    where
        T: Sized, // TODO: don't require T: Sized here. Problem: return type is T.
    {
        pearlite! { absurd }
    }
}
