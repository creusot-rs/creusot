use crate::{std::ops::Deref, *};

#[cfg_attr(feature = "contracts", creusot::builtins = "prelude.Ghost.ghost_ty")]
pub struct Ghost<T>(std::marker::PhantomData<T>)
where
    T: ?Sized;

impl<T: ?Sized> Deref for Ghost<T> {
    type Target = T;

    #[trusted]
    #[logic]
    #[creusot::builtins = "prelude.Ghost.inner"]
    fn deref(&self) -> &Self::Target {
        pearlite! { absurd }
    }
}

impl<T: ShallowModel + ?Sized> ShallowModel for Ghost<T> {
    type ShallowModelTy = T::ShallowModelTy;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { self.deref().shallow_model() }
    }
}

impl<T: ?Sized> Ghost<T> {
    #[trusted]
    #[logic]
    #[creusot::builtins = "prelude.Ghost.new"]
    pub fn new(_: T) -> Ghost<T> {
        pearlite! { absurd }
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "prelude.Ghost.inner"]
    pub fn inner(self) -> T
    where
        T: Sized, // TODO: don't require T: Sized here. Problem: return type is T.
    {
        pearlite! { absurd }
    }
}
