use crate::{std::ops::Deref, *};

#[rustc_diagnostic_item = "snapshot_ty"]
#[trusted]
pub struct Snapshot<T>(pub(crate) std::marker::PhantomData<T>)
where
    T: ?Sized;

impl<T: ?Sized> Deref for Snapshot<T> {
    type Target = T;

    #[trusted]
    #[logic]
    #[open(self)]
    #[rustc_diagnostic_item = "snapshot_deref"]
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
    #[ensures(&*result == &x)]
    #[rustc_diagnostic_item = "snapshot_new"]
    pub fn new(x: T) -> Snapshot<T> {
        pearlite! { absurd }
    }

    #[logic]
    #[open(self)]
    #[rustc_diagnostic_item = "snapshot_inner"]
    pub fn inner(self) -> T
    where
        T: Sized, // TODO: don't require T: Sized here. Problem: return type is T.
    {
        *self
    }
}
