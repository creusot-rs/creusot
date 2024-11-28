use crate::{std::ops::Deref, *};

#[trusted]
#[rustc_diagnostic_item = "snapshot_ty"]
#[cfg_attr(creusot, creusot::builtins = "prelude.prelude.Snapshot.snap_ty")]
pub struct Snapshot<T: ?Sized>(pub(crate) std::marker::PhantomData<T>);

impl<T: ?Sized> Deref for Snapshot<T> {
    type Target = T;

    #[trusted]
    #[logic]
    #[rustc_diagnostic_item = "snapshot_deref"]
    #[creusot::builtins = "prelude.prelude.Snapshot.inner"]
    fn deref(&self) -> &Self::Target {
        dead
    }
}

impl<T: View + ?Sized> View for Snapshot<T> {
    type ViewTy = T::ViewTy;

    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        pearlite! { self.deref().view() }
    }
}

impl<T: ?Sized> Clone for Snapshot<T> {
    #[pure]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        snapshot! { **self }
    }
}

impl<T: ?Sized> Copy for Snapshot<T> {}

impl<T: ?Sized> Snapshot<T> {
    #[trusted]
    #[logic]
    #[creusot::builtins = "prelude.prelude.Snapshot.new"]
    #[rustc_diagnostic_item = "snapshot_new"]
    pub fn new(_: T) -> Snapshot<T> {
        dead
    }

    #[trusted]
    #[logic]
    #[rustc_diagnostic_item = "snapshot_inner"]
    #[creusot::builtins = "prelude.prelude.Snapshot.inner"]
    pub fn inner(self) -> T
    where
        T: Sized, // TODO: don't require T: Sized here. Problem: return type is T.
    {
        dead
    }
}
