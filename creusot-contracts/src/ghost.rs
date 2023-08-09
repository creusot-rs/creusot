use crate::{std::ops::Deref, *};

#[cfg_attr(creusot, creusot::builtins = "prelude.Ghost.ghost_ty")]
pub struct Ghost<T>(std::marker::PhantomData<T>)
where
    T: ?Sized;

impl<T: ?Sized> Deref for Ghost<T> {
    type Target = T;

    #[trusted]
    #[ghost]
    #[open(self)]
    #[rustc_diagnostic_item = "ghost_deref"]
    #[creusot::builtins = "prelude.Ghost.inner"]
    fn deref(&self) -> &Self::Target {
        pearlite! { absurd }
    }
}

impl<T: ShallowModel + ?Sized> ShallowModel for Ghost<T> {
    type ShallowModelTy = T::ShallowModelTy;

    #[ghost]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { self.deref().shallow_model() }
    }
}

impl<T: ?Sized> Clone for Ghost<T> {
    fn clone(&self) -> Self {
        gh! { **self }
    }
}

impl<T: ?Sized> Copy for Ghost<T> {}

impl<T: ?Sized> Ghost<T> {
    #[trusted]
    #[ghost]
    #[open(self)]
    #[creusot::builtins = "prelude.Ghost.new"]
    pub fn new(_: T) -> Ghost<T> {
        pearlite! { absurd }
    }

    #[trusted]
    #[ghost]
    #[open(self)]
    #[rustc_diagnostic_item = "ghost_inner"]
    #[creusot::builtins = "prelude.Ghost.inner"]
    pub fn inner(self) -> T
    where
        T: Sized, // TODO: don't require T: Sized here. Problem: return type is T.
    {
        pearlite! { absurd }
    }
}
