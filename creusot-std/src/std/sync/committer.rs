#[cfg(feature = "sc-drf")]
use crate::std::sync::atomic_sc::ordering::SeqCst;
use crate::{
    ghost::{Perm, perm::PermTarget},
    logic::FMap,
    prelude::*,
    std::sync::{
        atomic::ordering::{LoadOrdering, StoreOrdering},
        view::{AcquireSyncView, HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
    },
};
use core::marker::PhantomData;
use core::sync::atomic::{Ordering as OrderingTy};

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

pub mod atomic_specs {
    use crate::{
        ghost::{Perm, perm::PermTarget},
        logic::FMap,
        prelude::*,
        std::sync::view::{AcquireSyncView, HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
    };

    #[logic(open, prophetic)]
    pub fn load_timestamp_in_view<C, T>(atomic : C, sync_view: &mut SyncView, t : Timestamp) -> bool
    where
        C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
    {
        pearlite!{
            let old_t = atomic.get_timestamp(*sync_view);
            let new_t = atomic.get_timestamp(^sync_view);
            old_t <= t && t <= new_t
        }
    }

    #[logic(open, prophetic)]
    pub fn load_reads_from_history<C, T>(own : &Perm<C>, thread_view : SyncView, val : T, t : Timestamp) -> bool 
    where
        C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
    {
        pearlite!{
            match own.val().get(t) {
                Some((v, v_view)) => v == val && v_view <= thread_view,
                None => false
            }
        }
    }

    #[logic(open, prophetic)]
    pub fn view_mono(sync_view: &mut SyncView) -> bool
    {
        pearlite!{
            *sync_view <= ^sync_view
        }
    }

    #[logic(open, prophetic)]
    pub fn load_acq_post<C, T>(atomic: C, own : &Perm<C>, sync_view: &mut SyncView, val : T, t : Timestamp) -> bool
    where
        C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
    {
        pearlite!{
            load_timestamp_in_view(atomic, sync_view, t) && load_reads_from_history(own, ^sync_view, val, t) && view_mono(sync_view)
        }
    }

    #[logic(open, prophetic)]
    pub fn load_rlx_post<C, T>(atomic : C, own : &Perm<C>, sync_view: &mut SyncView, val : T, t : Timestamp, acq_sync_view : AcquireSyncView) -> bool
    where
        C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
    {
        pearlite!{
            load_timestamp_in_view(atomic, sync_view, t) && load_reads_from_history(own, acq_sync_view@, val, t) && view_mono(sync_view)
        }
    }

    #[logic(open, prophetic)]
    // t here corresponds to self.timestamp() + 1 in the committer specs
    pub fn store_timestamp_in_view<C, T>(atomic : C, sync_view: &mut SyncView, t : Timestamp) -> bool
    where
        C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,

    {
        pearlite!{
            let old_t = atomic.get_timestamp(*sync_view);
            let new_t = atomic.get_timestamp(^sync_view);
            old_t < t && t <= new_t
        }
    }

    #[logic(open, prophetic)]
    pub fn store_inserts_in_history<C,T>(own : &mut Perm<C>, thread_view : SyncView, val : T, t : Timestamp) -> bool
    where
        C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
    {
        pearlite!{
            (*own).val().get(t) == None &&
                (^own).val() == (*own).val().insert(t, (val, thread_view)) &&
                (*own).ward() == (^own).ward()
        }
    }

    #[logic(open, prophetic)]
    pub fn store_rel_post<C, T>(atomic : C, own : &mut Perm<C>, sync_view: &mut SyncView, val : T, t : Timestamp) -> bool
    where
        C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
    {
        pearlite!{
            store_timestamp_in_view(atomic, sync_view, t) &&
                store_inserts_in_history(own, ^sync_view, val, t) &&
                view_mono(sync_view) && (*own).ward() == (^own).ward()
        }
    }

    #[logic(open, prophetic)]
    pub fn store_rlx_post<C, T>(atomic : C, own : &mut Perm<C>, sync_view: &mut SyncView, val : T, t : Timestamp, rel_view : ReleaseSyncView) -> bool
        where C: PermTarget<Value<'static> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'static,
    {
        pearlite!{
            store_timestamp_in_view(atomic, sync_view, t) &&
                store_inserts_in_history(own, rel_view@, val, t) &&
                view_mono(sync_view) && (*own).ward() == (^own).ward()
        }
    }
}
use atomic_specs::*;

impl<'a, C, T, Load : LoadOrdering, Store> Committer<C, T, Load, Store>
where
    C: PermTarget<Value<'a> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'a,
{
    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code.
    #[requires(!self.shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(self.ward(), own, sync_view, self.val_load(), self.timestamp()))]
    #[ensures(Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(self.ward(), own, sync_view, self.val_load(), self.timestamp(), result))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_load(&self, own: &Perm<C>, sync_view: &mut SyncView) -> AcquireSyncView {
        panic!("Should not be called outside ghost code")
    }
}

#[cfg(feature = "sc-drf")]
impl<'a, C, Store> Committer<C, C::Value<'a>, SeqCst, Store>
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

impl<'a, C, T, Load, Store: StoreOrdering> Committer<C, T, Load, Store>
where
    C: PermTarget<Value<'a> = FMap<Timestamp, (T, SyncView)>> + HasTimestamp + 'a,
{
    /// 'Shoot' the committer (Relaxed)
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((*self).hist_inv(^self))]
    #[ensures((^self).shot_store())]
    #[ensures(Store::ORDERING == OrderingTy::Release ==> store_rel_post(self.ward(), own, sync_view, self.val_store(), self.timestamp() + 1))]
    #[ensures(Store::ORDERING == OrderingTy::Relaxed ==> store_rlx_post(self.ward(), own, sync_view, self.val_store(), self.timestamp() + 1, rel_view))]
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

#[cfg(feature = "sc-drf")]
impl<'a, C, Load> Committer<C, C::Value<'a>, Load, SeqCst>
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
