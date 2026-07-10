#![allow(unused_imports)]
use crate::{
    ghost::{FnGhost, Perm, perm::PermTarget},
    logic::FMap,
    prelude::*,
    std::sync::{
        committer::Committer,
        view::{AcquireSyncView, HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
        atomic::{ordering::{Ordering, LoadOrdering, StoreOrdering, UpdateOrdering, Relaxed, Acquire, Release, AcqRel}, AtomicBool, AtomicPtr, AtomicI8, AtomicU8, AtomicI16, AtomicI32, AtomicI64, AtomicIsize, AtomicU16, AtomicU32, AtomicU64, AtomicUsize},
    },
};
use core::sync::atomic::{Ordering as OrderingTy};

macro_rules! extend_atomic {
    ($( ($type:ty, $atomic_type:ident $(< $T:ident >)?) ),+) => { $(

        impl $(< $T >)? $atomic_type $(< $T >)? {

            #[logic(prophetic)]
            pub fn load_timestamp_in_view(&self, sync_view: &mut SyncView, t : Timestamp) -> bool {
                pearlite!{
                    let old_t = self.get_timestamp(*sync_view);
                    let new_t = self.get_timestamp(^sync_view);
                    old_t <= t && t <= new_t
                }
            }

            #[logic(prophetic)]
            pub fn load_reads_from_history(own : &Perm<$atomic_type $(< $T >)?>, thread_view : SyncView, val : $type, t : Timestamp) -> bool {
                pearlite!{
                    match own.val().get(t) {
                        Some((v, v_view)) => v == val && v_view <= thread_view,
                        None => false
                    }
                }
            }

            #[logic(prophetic)]
            pub fn view_mono(sync_view: &mut SyncView) -> bool {
                pearlite!{
                    *sync_view <= ^sync_view
                }
            }

            #[logic(prophetic)]
            pub fn load_acq_post(&self, own : &Perm<$atomic_type $(< $T >)?>, sync_view: &mut SyncView, val : $type, t : Timestamp) -> bool {
                pearlite!{
                    self.load_timestamp_in_view(sync_view, t) && Self::load_reads_from_history(own, ^sync_view, val, t) && Self::view_mono(sync_view)
                }
            }

            #[logic(prophetic)]
            pub fn load_rlx_post(&self, own : &Perm<$atomic_type $(< $T >)?>, sync_view: &mut SyncView, val : $type, t : Timestamp, acq_sync_view : AcquireSyncView) -> bool {
                pearlite!{
                    self.load_timestamp_in_view(sync_view, t) && Self::load_reads_from_history(own, acq_sync_view@, val, t) && Self::view_mono(sync_view)
                }
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::load`].")]
            #[requires(*self == *own.ward())]
            #[ensures(self.load_acq_post(*own, *sync_view, result.0, *result.1))]
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn acq_load(&self, own: Ghost<&Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>) -> ($type, Snapshot<Timestamp>)
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                let val = self.load(ghost! { |c: &Committer<_, $type, Acquire, _>| {
                    c.shoot_load(*own, *sync_view);
                    ts = snapshot!(c.timestamp());
                } });
                (val, ts)
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::load`].")]
            #[requires(*self == *own.ward())]
            #[ensures(self.load_rlx_post(*own, *sync_view, result.0, *result.1, *result.2))]
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn rlx_load(&self, own: Ghost<&Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>) -> ($type, Snapshot<Timestamp>, Ghost<AcquireSyncView>)
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                let mut acq_sync_view_opt = ghost!(None);
                let val = self.load(ghost! { |c: &Committer<_, $type, Relaxed, _>| {

                    let acq_sync_view = c.shoot_load(*own, *sync_view);
                    ts = snapshot!(c.timestamp());
                    acq_sync_view_opt = ghost!(Some(acq_sync_view));
                } });
                (val, ts, ghost!(acq_sync_view_opt.unwrap()))
            }

            #[logic(prophetic)]
            // t here corresponds to self.timestamp() + 1 in the committer specs
            pub fn store_timestamp_in_view(&self, sync_view: &mut SyncView, t : Timestamp) -> bool {
                pearlite!{
                    let old_t = self.get_timestamp(*sync_view);
                    let new_t = self.get_timestamp(^sync_view);
                    old_t < t && t <= new_t
                }
            }

            #[logic(prophetic)]
            pub fn store_inserts_in_history(own : &mut Perm<$atomic_type $(< $T >)?>, thread_view : SyncView, val : $type, t : Timestamp) -> bool {
                pearlite!{
                    (*own).val().get(t) == None &&
                    (^own).val() == (*own).val().insert(t, (val, thread_view)) &&
                    (*own).ward() == (^own).ward()
                }
            }

            #[logic(prophetic)]
            pub fn store_rel_post(&self, own : &mut Perm<$atomic_type $(< $T >)?>, sync_view: &mut SyncView, val : $type, t : Timestamp) -> bool {
                pearlite!{
                    self.store_timestamp_in_view(sync_view, t) &&
                        Self::store_inserts_in_history(own, ^sync_view, val, t) &&
                        Self::view_mono(sync_view) && (*own).ward() == (^own).ward()
                }
            }

            #[logic(prophetic)]
            pub fn store_rlx_post(&self, own : &mut Perm<$atomic_type $(< $T >)?>, sync_view: &mut SyncView, val : $type, t : Timestamp, rel_view : ReleaseSyncView) -> bool {
                pearlite!{
                    self.store_timestamp_in_view(sync_view, t) &&
                    Self::store_inserts_in_history(own, rel_view@, val, t) &&
                    Self::view_mono(sync_view) && (*own).ward() == (^own).ward()
                }
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::store`].")]
            #[requires(*self == *own.ward())]
            #[ensures(self.store_rel_post(*own, *sync_view, val, *result))]
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn rel_store<F, Store: StoreOrdering>(&self, val: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>) -> Snapshot<Timestamp>
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                self.store(val, ghost!{ |c : &mut Committer<_, $type, _, Release> | {
                    c.shoot_store(*own, *sync_view);
                    ts = snapshot!(c.timestamp() + 1);
                }
                });
                ts
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::store`].")]
            #[requires(*self == *own.ward())]
            #[ensures(self.store_rlx_post(*own, *sync_view, val, *result, *rel_view))]
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn rlx_store<F, Store: StoreOrdering>(&self, val: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<ReleaseSyncView>) -> Snapshot<Timestamp>
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                self.store(val, ghost!{ |c : &mut Committer<_, $type, _, Relaxed> | {
                    c.shoot_store(*own, *sync_view, *rel_view);
                    ts = snapshot!(c.timestamp() + 1);
                }
                });
                ts
            }
        }

    )* };
}

#[cfg(target_has_atomic = "8")]
extend_atomic!((bool, AtomicBool));
// FIXME the compiler rejects this because of issues with T's lifetime
// #[cfg(target_has_atomic = "ptr")]
// extend_atomic!((*mut T, AtomicPtr<T>));

#[cfg(target_has_atomic = "8")]
extend_atomic!((i8, AtomicI8));
extend_atomic!((u8, AtomicU8));
#[cfg(target_has_atomic = "16")]
extend_atomic!((i16, AtomicI16));
extend_atomic!((u16, AtomicU16));
#[cfg(target_has_atomic = "32")]
extend_atomic!((i32, AtomicI32));
extend_atomic!((u32, AtomicU32));
#[cfg(target_has_atomic = "64")]
extend_atomic!((i64, AtomicI64));
extend_atomic!((u64, AtomicU64));
