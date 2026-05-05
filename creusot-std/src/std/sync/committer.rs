use crate::{
    ghost::{PermTarget, perm::Perm},
    logic::FMap,
    prelude::*,
    std::sync::{
        atomic::Ordering,
        view::{AcquireSyncView, HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
    },
};
use core::marker::PhantomData;

/// Wrapper around a single atomic operation, where multiple ghost steps can be performed.
///
/// Note: For load-only accesses, this committer has no observable effect on ghost ressources.
/// Thus, it is optional to shoot it, and nothing prevent the user from shooting it several times.
// This trick is correct for SC accesses under SC-DRF, and for Rel/Acq/Rlx and Rlx accesses, but
// perhaps not for C20's SC accesses.
#[opaque]
pub struct Committer<C: PermTarget, T, Load, Store>(PhantomData<(C, T, Load, Store)>);

impl<C: PermTarget, T, Load, Store> Committer<C, T, Load, Store> {
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
            && self.timestamp() == other.timestamp()
    }
}

impl<C, T, Store> Committer<C, T, Ordering::Relaxed, Store>
where
    C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
{
    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code.
    #[requires(!self.shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(*sync_view <= ^sync_view)]
    #[ensures(self.ward().get_timestamp(*sync_view) <= self.timestamp())]
    #[ensures(self.timestamp() <= self.ward().get_timestamp(^sync_view))]
    #[ensures(own.val().get(self.timestamp()) == Some((self.val_load(), result@)))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_load(&self, own: &Perm<C>, sync_view: &mut SyncView) -> AcquireSyncView {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, T, Store> Committer<C, T, Ordering::Acquire, Store>
where
    C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
{
    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code.
    #[requires(!self.shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(*sync_view <= ^sync_view)]
    #[ensures(self.ward().get_timestamp(*sync_view) <= self.timestamp())]
    #[ensures(self.timestamp() <= self.ward().get_timestamp(^sync_view))]
    #[ensures(match own.val().get(self.timestamp()) {
        Some((v, v_view)) => v == self.val_load() && v_view <= ^sync_view,
        None => false
    })]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_load(&self, own: &Perm<C>, sync_view: &mut SyncView) {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, Store> Committer<C, C::Value<'static>, Ordering::SeqCst, Store>
where
    C: PermTarget,
{
    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code.
    #[requires(!self.shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(self.val_load() == own.val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_load(&self, own: &Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, T, Load> Committer<C, T, Load, Ordering::Relaxed>
where
    C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
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
    #[ensures((*self).ward().get_timestamp(*sync_view) <= self.timestamp())]
    #[ensures(self.timestamp() < (*self).ward().get_timestamp(^sync_view))]
    #[ensures((*own).val().get(self.timestamp() + 1) == None)]
    #[ensures((^own).val() == (*own).val().insert(self.timestamp() + 1, ((*self).val_store(), rel_view@)))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_store(
        &mut self,
        own: &mut Perm<C>,
        sync_view: &mut SyncView,
        rel_view: ReleaseSyncView,
    ) {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, T, Load> Committer<C, T, Load, Ordering::Release>
where
    C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
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
    #[ensures((*self).ward().get_timestamp(*sync_view) <= self.timestamp())]
    #[ensures(self.timestamp() < (*self).ward().get_timestamp(^sync_view))]
    #[ensures((*own).val().get(self.timestamp() + 1) == None)]
    #[ensures((^own).val() == (*own).val().insert(self.timestamp() + 1, ((*self).val_store(), ^sync_view)))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_store(&mut self, own: &mut Perm<C>, sync_view: &mut SyncView) {
        panic!("Should not be called outside ghost code")
    }
}

impl<C, Load> Committer<C, C::Value<'static>, Load, Ordering::SeqCst>
where
    C: PermTarget,
{
    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((*self).hist_inv(^self))]
    #[ensures((^self).shot_store())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures((^own).val() == (*self).val_store())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_store(&mut self, own: &mut Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}
