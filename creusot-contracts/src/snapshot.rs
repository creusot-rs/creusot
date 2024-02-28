use crate::{std::ops::Deref, *};

#[cfg_attr(creusot, creusot::builtins = "prelude.Snapshot.snap_ty")]
pub struct Snapshot<T>(pub(crate) std::marker::PhantomData<T>)
where
    T: ?Sized;

impl<T: ?Sized> Deref for Snapshot<T> {
    type Target = T;

    #[trusted]
    #[logic]
    #[open(self)]
    #[rustc_diagnostic_item = "snapshot_deref"]
    #[creusot::builtins = "prelude.Snapshot.inner"]
    fn deref(&self) -> &Self::Target {
        pearlite! { absurd }
    }
}

impl<T: ShallowModel + ?Sized> ShallowModel for Snapshot<T> {
    type ShallowModelTy = T::ShallowModelTy;

    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { self.deref().shallow_model() }
    }
}

impl<T: ?Sized> Clone for Snapshot<T> {
    fn clone(&self) -> Self {
        snapshot! { **self }
    }
}

impl<T: ?Sized> Copy for Snapshot<T> {}

impl<T: ?Sized> Snapshot<T> {
    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "prelude.Snapshot.new"]
    pub fn new(_: T) -> Snapshot<T> {
        pearlite! { absurd }
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[rustc_diagnostic_item = "snapshot_inner"]
    #[creusot::builtins = "prelude.Snapshot.inner"]
    pub fn inner(self) -> T
    where
        T: Sized, // TODO: don't require T: Sized here. Problem: return type is T.
    {
        pearlite! { absurd }
    }
}
