#![allow(unused_imports)]
use crate::{
    ghost::{FnGhost, Perm, perm::PermTarget},
    logic::FMap,
    prelude::*,
    std::sync::{
        committer::{Committer, atomic_specs::*},
        view::{AcquireSyncView, HasTimestamp, ReleaseSyncView, SyncView, Timestamp},
        atomic::{ordering::{Ordering, LoadOrdering, StoreOrdering, UpdateOrdering, Relaxed, Acquire, Release, AcqRel}, AtomicBool, AtomicPtr, AtomicI8, AtomicU8, AtomicI16, AtomicI32, AtomicI64, AtomicIsize, AtomicU16, AtomicU32, AtomicU64, AtomicUsize},
    },
};
use core::sync::atomic::{Ordering as OrderingTy};

macro_rules! extend_atomic {
    ($( ($type:ty, $atomic_type:ident $(< $T:ident >)?) ),+) => { $(

        impl $(< $T >)? $atomic_type $(< $T >)? {

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::load`].")]
            #[requires(*self == *own.ward())]
            #[ensures(Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(*self, *own, *sync_view, result.0, *result.1))]
            #[ensures(Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(*self, *own, *sync_view, result.0, *result.1, *result.2))]
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn wrap_load<Load: LoadOrdering>(&self, own: Ghost<&Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>) -> ($type, Snapshot<Timestamp>, Ghost<AcquireSyncView>)
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                let mut acq_sync_view_opt = ghost!(None);
                let val = self.load(ghost! { |c: &Committer<_, $type, Load, _>| {
                    let acq_sync_view = c.shoot_load(*own, *sync_view);
                    ts = snapshot!(c.timestamp());
                    acq_sync_view_opt = ghost!(Some(acq_sync_view));
                } });
                (val, ts, ghost!(acq_sync_view_opt.unwrap()))
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::store`].")]
            #[requires(*self == *own.ward())]
            #[ensures(Store::ORDERING == OrderingTy::Release ==> store_rel_post(*self, *own, *sync_view, val, *result))]
            #[ensures(Store::ORDERING == OrderingTy::Relaxed ==> store_rlx_post(*self, *own, *sync_view, val, *result, *rel_view))]
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn wrap_store<Store: StoreOrdering>(&self, val: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<ReleaseSyncView>) -> Snapshot<Timestamp>
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                self.store(val, ghost!{ |c : &mut Committer<_, $type, _, Store> | {
                    c.shoot_store(*own, *sync_view, *rel_view);
                    ts = snapshot!(c.timestamp() + 1);
                }
                });
                ts
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::compare_exchange`].")]
            #[doc = ""]
            #[doc = "The load and the store are always sequentially consistent."]
            #[requires(*self == *own.ward())]
            #[ensures(
                match result.0 {
                    Ok(v) => {
                        v.deep_model() == current.deep_model() &&
                        Success::Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(*self, *own, *sync_view, v, *result.1) &&
                        Success::Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(*self, *own, *sync_view, v, *result.1, *result.2) &&
                        Success::Store::ORDERING == OrderingTy::Release ==> store_rel_post(*self, *own, *sync_view, v, *result.1 + 1) &&
                        Success::Store::ORDERING == OrderingTy::Relaxed ==> store_rlx_post(*self, *own, *sync_view, v, *result.1 + 1, *rel_view)
                    },
                    Err(v) => {
                        v.deep_model() != current.deep_model() &&
                        Success::Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(*self, *own, *sync_view, v, *result.1) &&
                        Success::Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(*self, *own, *sync_view, v, *result.1, *result.2)
                    }
                }
            )]
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn wrap_compare_exchange<Success: UpdateOrdering, Failure: LoadOrdering>(&self, current: $type, new: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<ReleaseSyncView>) -> (Result<$type, $type>, Snapshot<Timestamp>, Ghost<AcquireSyncView>)
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                let mut acq_sync_view_opt = ghost!(None);
                let f = ghost!(|c : Result<&mut Committer<_, $type, Success::Load, Success::Store>, &Committer<_, $type, Failure, _>>| {
                    match c {
                        Ok(c) => {
                            let acq_sync_view = c.shoot_load(*own, *sync_view);
                            ts = snapshot!(c.timestamp());
                            acq_sync_view_opt = ghost!(Some(acq_sync_view));
                            c.shoot_store(*own, *sync_view, *rel_view);
                        },
                        Err(c) => {
                            let acq_sync_view = c.shoot_load(*own, *sync_view);
                            ts = snapshot!(c.timestamp());
                            acq_sync_view_opt = ghost!(Some(acq_sync_view));
                        }
                    }
                });
                match self.compare_exchange::<_, Success, Failure>(current, new, f) {
                    Ok(v) => {
                        return (Ok(v), ts, ghost!(acq_sync_view_opt.unwrap()));
                    },
                    Err(v) => {
                        return (Err(v), ts, ghost!(acq_sync_view_opt.unwrap()));
                    }
                }
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::compare_exchange_weak`].")]
            #[doc = ""]
            #[doc = "The load and the store are always sequentially consistent."]
            #[requires(*self == *own.ward())]
            #[ensures(
                match result.0 {
                    Ok(v) => {
                        v.deep_model() == current.deep_model() &&
                        Success::Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(*self, *own, *sync_view, v, *result.1) &&
                        Success::Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(*self, *own, *sync_view, v, *result.1, *result.2) &&
                        Success::Store::ORDERING == OrderingTy::Release ==> store_rel_post(*self, *own, *sync_view, v, *result.1 + 1) &&
                        Success::Store::ORDERING == OrderingTy::Relaxed ==> store_rlx_post(*self, *own, *sync_view, v, *result.1 + 1, *rel_view)
                    },
                    Err(v) => {
                        Success::Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(*self, *own, *sync_view, v, *result.1) &&
                        Success::Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(*self, *own, *sync_view, v, *result.1, *result.2)
                    }
                }
            )]
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn wrap_compare_exchange_weak<Success: UpdateOrdering, Failure: LoadOrdering>(&self, current: $type, new: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<ReleaseSyncView>) -> (Result<$type, $type>, Snapshot<Timestamp>, Ghost<AcquireSyncView>)
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                let mut acq_sync_view_opt = ghost!(None);
                let f = ghost!(|c : Result<&mut Committer<_, $type, Success::Load, Success::Store>, &Committer<_, $type, Failure, _>>| {
                    match c {
                        Ok(c) => {
                            let acq_sync_view = c.shoot_load(*own, *sync_view);
                            ts = snapshot!(c.timestamp());
                            acq_sync_view_opt = ghost!(Some(acq_sync_view));
                            c.shoot_store(*own, *sync_view, *rel_view);
                        },
                        Err(c) => {
                            let acq_sync_view = c.shoot_load(*own, *sync_view);
                            ts = snapshot!(c.timestamp());
                            acq_sync_view_opt = ghost!(Some(acq_sync_view));
                        }
                    }
                });
                match self.compare_exchange_weak::<_, Success, Failure>(current, new, f) {
                    Ok(v) => {
                        return (Ok(v), ts, ghost!(acq_sync_view_opt.unwrap()));
                    },
                    Err(v) => {
                        return (Err(v), ts, ghost!(acq_sync_view_opt.unwrap()));
                    }
                }
            }

        }

    )* };
}

#[cfg(target_has_atomic = "8")]
extend_atomic!((bool, AtomicBool));
#[cfg(target_has_atomic = "ptr")]
extend_atomic!((*mut T, AtomicPtr<T>));

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
