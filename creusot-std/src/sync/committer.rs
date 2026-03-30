use crate::{
    ghost::{Container, perm::Perm},
    logic::FMap,
    prelude::*,
    std::sync::atomic::Ordering,
    sync::sync_view::{AcquireSyncView, HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
};
use core::marker::PhantomData;

/// Wrapper around a single atomic operation, where multiple ghost steps can be performed.
///
/// Note: this committer has no observable effect on ghost ressources. Thus, it is optional to shoot
/// it, and nothing prevent the user from shooting it several times.
// This trick is correct for SC accesses under SC-DRF, and for Rel/Acq/Rlx and Rlx accesses, but
// perhaps not for C20's SC accesses.
#[opaque]
pub struct Committer<C: Container<Value: Sized>, T, Load, Store>(PhantomData<(C, T, Load, Store)>);

impl<C: Container<Value: Sized>, T, Load, Store> Committer<C, T, Load, Store> {
    /// Identity of the committer
    ///
    /// This is used so that we can only use the committer with the right [`AtomicOwn`].
    #[logic(opaque)]
    pub fn ward(self) -> C {
        dead
    }

    /// Timestamp of the latest load, before any store.
    ///
    /// This is used for an update operation.
    #[logic(opaque)]
    pub fn timestamp(self) -> Timestamp {
        dead
    }

    /// Value read from the atomic operation.
    #[logic(opaque)]
    pub fn val_load(self) -> T {
        dead
    }

    /// Value written by the atomic operation.
    #[logic(opaque)]
    pub fn val_store(self) -> T {
        dead
    }

    /// Status of the committer
    #[logic(opaque)]
    pub fn shot_store(self) -> bool {
        dead
    }

    #[logic(open, inline)]
    pub fn hist_inv(self, other: Self) -> bool {
        self.ward() == other.ward()
            && self.val_load() == other.val_load()
            && self.val_store() == other.val_store()
    }
}

impl<C, T, Store> Committer<C, T, Ordering::Relaxed, Store>
where
    C: Container<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
{
    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code.
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(*sync_view <= ^sync_view)]
    #[ensures(self.ward().get_timestamp(*sync_view) <= result.0)]
    #[ensures(result.0 <= self.ward().get_timestamp(^sync_view))]
    #[ensures(match own.val().get(result.0) {
        Some((v, v_view)) => v == self.val_load() && v_view <= result.1.view(),
        None => false
    })]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_load(
        &self,
        own: &Perm<C>,
        sync_view: &mut SyncView,
    ) -> (Timestamp, AcquireSyncView) {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, T, Store> Committer<C, T, Ordering::Acquire, Store>
where
    C: Container<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
{
    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code.
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(*sync_view <= ^sync_view)]
    #[ensures(self.ward().get_timestamp(*sync_view) <= result)]
    #[ensures(result <= self.ward().get_timestamp(^sync_view))]
    #[ensures(match own.val().get(result) {
        Some((v, v_view)) => v == self.val_load() && v_view <= ^sync_view,
        None => false
    })]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_load(&self, own: &Perm<C>, sync_view: &mut SyncView) -> Timestamp {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, Store> Committer<C, C::Value, Ordering::SeqCst, Store>
where
    C: Container<Value: Sized>,
{
    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code.
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(self.val_load() == *own.val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_load(&self, own: &Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, T, Load> Committer<C, T, Load, Ordering::Relaxed>
where
    C: Container<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
{
    /// 'Shoot' the committer (Relaxed)
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((*self).hist_inv(^self))]
    #[ensures((^self).shot_store())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures(*sync_view <= ^sync_view)]
    #[ensures((*self).ward().get_timestamp(*sync_view) < result)]
    #[ensures(result <= (*self).ward().get_timestamp(^sync_view))]
    #[ensures((*own).val().get(result) == None)]
    #[ensures(*(^own).val() == (*own).val().insert(result, ((*self).val_store(), rel_view.view())))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_store(
        &mut self,
        own: &mut Perm<C>,
        sync_view: &mut SyncView,
        rel_view: ReleaseSyncView,
    ) -> Timestamp {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, T, Load> Committer<C, T, Load, Ordering::Release>
where
    C: Container<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
{
    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((*self).hist_inv(^self))]
    #[ensures((^self).shot_store())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures(*sync_view <= ^sync_view)]
    #[ensures((*self).ward().get_timestamp(*sync_view) < result)]
    #[ensures(result <= (*self).ward().get_timestamp(^sync_view))]
    #[ensures((*own).val().get(result) == None)]
    #[ensures(*(^own).val() == (*own).val().insert(result, ((*self).val_store(), ^sync_view)))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_store(&mut self, own: &mut Perm<C>, sync_view: &mut SyncView) -> Timestamp {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, Load> Committer<C, C::Value, Load, Ordering::SeqCst>
where
    C: Container<Value: Sized>,
{
    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((*self).hist_inv(^self))]
    #[ensures((^self).shot_store())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures(*(^own).val() == (*self).val_store())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_store(&mut self, own: &mut Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}
