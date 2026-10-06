#![cfg_attr(not(creusot), allow(unused_imports))]
#[cfg(feature = "sc-drf")]
use crate::std::sync::atomic_sc::ordering::SeqCst;
use crate::{
    ghost::{Perm, perm::PermTarget},
    logic::FMap,
    prelude::*,
    std::sync::{
        atomic::ordering::{LoadOrdering, StoreOrdering},
        view::{HasTimestamp, SyncView, Timestamp},
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

pub mod atomic_specs {
    use crate::{
        ghost::{Perm, perm::PermTarget},
        logic::FMap,
        prelude::*,
        std::sync::{
            atomic::ordering::{LoadOrdering, StoreOrdering},
            view::{HasTimestamp, SyncView, Timestamp},
        },
    };

    #[logic(open, prophetic)]
    pub fn load_timestamp_in_view<C, T>(
        atomic: C,
        sync_view: &mut SyncView,
        t: Timestamp,
    ) -> bool
    where
        C: PermTarget<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
    {
        pearlite! {
            let old_t = atomic.get_timestamp(*sync_view);
            let new_t = atomic.get_timestamp(^sync_view);
            old_t <= t && t <= new_t
        }
    }

    #[logic(open, prophetic)]
    pub fn view_mono(sync_view: &mut SyncView) -> bool {
        pearlite! {
            *sync_view <= ^sync_view
        }
    }

    #[logic(open, prophetic)]
    // t here corresponds to self.timestamp() + 1 in the committer specs
    pub fn store_timestamp_in_view<C, T>(
        atomic: C,
        sync_view: &mut SyncView,
        t: Timestamp,
    ) -> bool
    where
        C: PermTarget<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
    {
        pearlite! {
            let old_t = atomic.get_timestamp(*sync_view);
            let new_t = atomic.get_timestamp(^sync_view);
            old_t < t && t <= new_t
        }
    }

    /// Postcondition of a load with ordering `Load`, reading `val` at timestamp `t`, that moves the
    /// thread view from `old_view` to `new_view`.
    #[logic(open, prophetic)]
    pub fn load_post<Load: LoadOrdering, C, T>(
        atomic: C,
        own: &Perm<C>,
        old_view: SyncView,
        new_view: SyncView,
        val: T,
        t: Timestamp,
        acq_view: Load::Acq,
    ) -> bool
    where
        C: PermTarget<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
    {
        pearlite! {
            old_view <= new_view &&
                atomic.get_timestamp(old_view) <= t &&
                t <= atomic.get_timestamp(new_view) &&
                Load::view_acquired(own.val(), new_view, val, t, acq_view)
        }
    }

    /// Postcondition of a store with ordering `Store`, writing `val` at timestamp `t`, that moves the
    /// thread view from `old_view` to `new_view`.
    #[logic(open, prophetic)]
    pub fn store_post<Store: StoreOrdering, C, T>(
        atomic: C,
        own: &mut Perm<C>,
        old_view: SyncView,
        new_view: SyncView,
        val: T,
        t: Timestamp,
        rel_view: Store::Rel,
    ) -> bool
    where
        C: PermTarget<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
    {
        pearlite! {
            old_view <= new_view &&
                atomic.get_timestamp(old_view) < t &&
                t <= atomic.get_timestamp(new_view) &&
                Store::view_released((*own).val(), (^own).val(), new_view, val, t, rel_view) &&
                (*own).ward() == (^own).ward()
        }
    }

}
use atomic_specs::*;

// impl<C, T, Store> Committer<C, T, Relaxed, Store>
impl<C, T, Load: LoadOrdering, Store> Committer<C, T, Load, Store>
where
    C: PermTarget<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
{
    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code.
    #[requires(!self.shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures(load_post::<Load, C, T>(self.ward(), own, *sync_view, ^sync_view, self.val_load(), self.timestamp(), result))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_load(&self, own: &Perm<C>, sync_view: &mut SyncView) -> Load::Acq {
        panic!("Should not be called outside ghost code")
    }
}

#[cfg(feature = "sc-drf")]
impl<C, Store> Committer<C, C::Value, SeqCst, Store>
where
    C: PermTarget,
    C::Value: Sized,
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

// impl<C, T, Load> Committer<C, T, Load, Relaxed>
impl<C, T, Load, Store: StoreOrdering> Committer<C, T, Load, Store>
where
    C: PermTarget<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp,
{
    /// 'Shoot' the committer (Relaxed)
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot_store())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((*self).hist_inv(^self))]
    #[ensures((^self).shot_store())]
    #[ensures(store_post::<Store, C, T>(self.ward(), own, *sync_view, ^sync_view, self.val_store(), self.timestamp() + 1, rel_view))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot_store(
        &mut self,
        own: &mut Perm<C>,
        sync_view: &mut SyncView,
        rel_view: Store::Rel,
    ) {
        panic!("Should not be called outside ghost code")
    }
}

#[cfg(feature = "sc-drf")]
impl<C, Load> Committer<C, C::Value, Load, SeqCst>
where
    C: PermTarget,
    C::Value: Sized,
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
