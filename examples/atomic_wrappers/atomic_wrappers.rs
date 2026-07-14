// DEPTH 8
#![allow(dead_code)]

extern crate creusot_std;

use creusot_std::{
    ghost::Perm,
    prelude::*,
    std::sync::{
        committer::{Committer, atomic_specs::*},
        view::{AcquireSyncView, ReleaseSyncView, SyncView, Timestamp},
        atomic::{ordering::{Ordering, LoadOrdering, StoreOrdering, UpdateOrdering}, AtomicBool, AtomicPtr, AtomicI8, AtomicU8, AtomicI16, AtomicI32, AtomicI64, AtomicU16, AtomicU32, AtomicU64},
    },
};
use core::sync::atomic::{Ordering as OrderingTy};

macro_rules! wrap_atomic {
    ($( ($type:ty, $atomic_type:ident $(< $T:ident >)?, $atomic_wrapper_type:ident) ),+) => { $(

        pub struct $atomic_wrapper_type $(< $T >)?($atomic_type $(< $T >)?);

        impl $(< $T >)? $atomic_wrapper_type $(< $T >)? {
            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::load`].")]
            #[requires(self.0 == *own.ward())]
            #[ensures(Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(self.0, *own, *sync_view, result.0, *result.1))]
            #[ensures(Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(self.0, *own, *sync_view, result.0, *result.1, *result.2))]
            fn wrap_load<Load: LoadOrdering>(&self, own: Ghost<&Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>) -> ($type, Snapshot<Timestamp>, Ghost<AcquireSyncView>)
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                let mut acq_sync_view_opt = ghost!(None);
                let val = self.0.load(ghost! { |c: &Committer<_, $type, Load, _>| {
                    let acq_sync_view = c.shoot_load(*own, *sync_view);
                    ts = snapshot!(c.timestamp());
                    acq_sync_view_opt = ghost!(Some(acq_sync_view));
                } });
                (val, ts, ghost!(acq_sync_view_opt.unwrap()))
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::store`].")]
            #[requires(self.0 == *own.ward())]
            #[ensures(Store::ORDERING == OrderingTy::Release ==> store_rel_post(self.0, *own, *sync_view, val, *result))]
            #[ensures(Store::ORDERING == OrderingTy::Relaxed ==> store_rlx_post(self.0, *own, *sync_view, val, *result, *rel_view))]
            fn wrap_store<Store: StoreOrdering>(&self, val: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<ReleaseSyncView>) -> Snapshot<Timestamp>
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                self.0.store(val, ghost!{ |c : &mut Committer<_, $type, _, Store> | {
                    c.shoot_store(*own, *sync_view, *rel_view);
                    ts = snapshot!(c.timestamp() + 1);
                }
                });
                ts
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::compare_exchange`].")]
            #[doc = ""]
            #[doc = "The load and the store are always sequentially consistent."]
            #[requires(self.0 == *own.ward())]
            #[ensures(
                match result.0 {
                    Ok(v) => {
                        v.deep_model() == current.deep_model() &&
                            Success::Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(self.0, *own, *sync_view, v, *result.1) &&
                            Success::Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(self.0, *own, *sync_view, v, *result.1, *result.2) &&
                            Success::Store::ORDERING == OrderingTy::Release ==> store_rel_post(self.0, *own, *sync_view, v, *result.1 + 1) &&
                            Success::Store::ORDERING == OrderingTy::Relaxed ==> store_rlx_post(self.0, *own, *sync_view, v, *result.1 + 1, *rel_view)
                    },
                    Err(v) => {
                        v.deep_model() != current.deep_model() &&
                            Success::Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(self.0, *own, *sync_view, v, *result.1) &&
                            Success::Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(self.0, *own, *sync_view, v, *result.1, *result.2)
                    }
                }
            )]
            fn wrap_compare_exchange<Success: UpdateOrdering, Failure: LoadOrdering>(&self, current: $type, new: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<ReleaseSyncView>) -> (Result<$type, $type>, Snapshot<Timestamp>, Ghost<AcquireSyncView>)
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
                match self.0.compare_exchange::<_, Success, Failure>(current, new, f) {
                    Ok(v) => {
                        return (Ok(v), ts, ghost!(acq_sync_view_opt.unwrap()));
                    },
                    Err(v) => {
                        return (Err(v), ts, ghost!(acq_sync_view_opt.unwrap()));
                    }
                }
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::compare_exchange`].")]
            #[doc = ""]
            #[doc = "The load and the store are always sequentially consistent."]
            #[requires(self.0 == *own.ward())]
            #[ensures(
                match result.0 {
                    Ok(v) => {
                        v.deep_model() == current.deep_model() &&
                            Success::Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(self.0, *own, *sync_view, v, *result.1) &&
                            Success::Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(self.0, *own, *sync_view, v, *result.1, *result.2) &&
                            Success::Store::ORDERING == OrderingTy::Release ==> store_rel_post(self.0, *own, *sync_view, v, *result.1 + 1) &&
                            Success::Store::ORDERING == OrderingTy::Relaxed ==> store_rlx_post(self.0, *own, *sync_view, v, *result.1 + 1, *rel_view)
                    },
                    Err(v) => {
                        Success::Load::ORDERING == OrderingTy::Acquire ==> load_acq_post(self.0, *own, *sync_view, v, *result.1) &&
                            Success::Load::ORDERING == OrderingTy::Relaxed ==> load_rlx_post(self.0, *own, *sync_view, v, *result.1, *result.2)
                    }
                }
            )]
            fn wrap_compare_exchange_weak<Success: UpdateOrdering, Failure: LoadOrdering>(&self, current: $type, new: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<ReleaseSyncView>) -> (Result<$type, $type>, Snapshot<Timestamp>, Ghost<AcquireSyncView>)
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
                match self.0.compare_exchange_weak::<_, Success, Failure>(current, new, f) {
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
wrap_atomic!((bool, AtomicBool, AtomicBoolWrapper));
#[cfg(target_has_atomic = "ptr")]
wrap_atomic!((*mut T, AtomicPtr<T>, AtomicPtrWrapper));

#[cfg(target_has_atomic = "8")]
wrap_atomic!((i8, AtomicI8, AtomicI8Wrapper));
wrap_atomic!((u8, AtomicU8, AtomicU8Wrapper));
#[cfg(target_has_atomic = "16")]
wrap_atomic!((i16, AtomicI16, AtomicI16Wrapper));
wrap_atomic!((u16, AtomicU16, AtomicU16Wrapper));
#[cfg(target_has_atomic = "32")]
wrap_atomic!((i32, AtomicI32, AtomicI32Wrapper));
wrap_atomic!((u32, AtomicU32, AtomicU32Wrapper));
#[cfg(target_has_atomic = "64")]
wrap_atomic!((i64, AtomicI64, AtomicI64Wrapper));
wrap_atomic!((u64, AtomicU64, AtomicU64Wrapper));
