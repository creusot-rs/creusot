// DEPTH 8
#![allow(dead_code)]

extern crate creusot_std;

use creusot_std::{
    ghost::Perm,
    prelude::*,
    std::sync::{
        atomic::{
            AtomicBool, AtomicI8, AtomicI16, AtomicI32, AtomicI64, AtomicPtr, AtomicU8, AtomicU16,
            AtomicU32, AtomicU64,
            ordering::{LoadOrdering, StoreOrdering, UpdateOrdering},
        },
        committer::Committer,
        view::{SyncView, Timestamp},
    },
};

macro_rules! wrap_atomic {
    ($( ($type:ty, $atomic_type:ident $(< $T:ident >)?, $atomic_wrapper_type:ident) ),+) => { $(

        pub struct $atomic_wrapper_type $(< $T >)?($atomic_type $(< $T >)?);

        impl $(< $T >)? $atomic_wrapper_type $(< $T >)? {
            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::load`].")]
            #[requires(self.0 == *own.ward())]
            #[ensures(Load::load_post(self.0, *own, *sync_view, result.0, *result.1, *result.2))]
            fn wrap_load<Load: LoadOrdering>(&self, own: Ghost<&Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>) -> ($type, Snapshot<Timestamp>, Ghost<Load::Acq>)
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                let mut acq_view_opt = ghost!(None);
                let val = self.0.load(ghost! { |c: &Committer<_, $type, Load, _>| {
                    let acq_view = c.shoot_load(*own, *sync_view);
                    ts = snapshot!(c.timestamp());
                    acq_view_opt = ghost!(Some(acq_view));
                } });
                (val, ts, ghost!(acq_view_opt.unwrap()))
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::store`].")]
            #[requires(self.0 == *own.ward())]
            #[ensures(Store::store_post(self.0, *own, *sync_view, val, *result, *rel_view))]
            fn wrap_store<Store: StoreOrdering>(&self, val: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<Store::Rel>) -> Snapshot<Timestamp>
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
                match (result.0, *result.2) {
                    (Ok(v), Ok(acq_view)) =>
                        v.deep_model() == current.deep_model() &&
                        Success::Load::load_post(self.0, *own, *sync_view, v, *result.1, acq_view) &&
                        Success::Store::store_post(self.0, *own, *sync_view, new, *result.1 + 1, *rel_view),
                    (Err(v), Err(acq_view)) =>
                        v.deep_model() != current.deep_model() &&
                        Failure::load_post(self.0, *own, *sync_view, v, *result.1, acq_view),
                    _ => false,
                }
            )]
            fn wrap_compare_exchange<Success: UpdateOrdering, Failure: LoadOrdering>(&self, current: $type, new: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<<Success::Store as StoreOrdering>::Rel>) -> (Result<$type, $type>, Snapshot<Timestamp>, Ghost<Result<<Success::Load as LoadOrdering>::Acq, Failure::Acq>>)
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                let mut acq_view_opt = ghost!(None);
                let f = ghost!(|c : Result<&mut Committer<_, $type, Success::Load, Success::Store>, &Committer<_, $type, Failure, _>>| {
                    match c {
                        Ok(c) => {
                            let acq_view = c.shoot_load(*own, *sync_view);
                            ts = snapshot!(c.timestamp());
                            acq_view_opt = ghost!(Some(Ok(acq_view)));
                            c.shoot_store(*own, *sync_view, *rel_view);
                        },
                        Err(c) => {
                            let acq_view = c.shoot_load(*own, *sync_view);
                            ts = snapshot!(c.timestamp());
                            acq_view_opt = ghost!(Some(Err(acq_view)));
                        }
                    }
                });
                let res = self.0.compare_exchange::<_, Success, Failure>(current, new, f);
                (res, ts, ghost!(acq_view_opt.unwrap()))
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::compare_exchange_weak`].")]
            #[doc = ""]
            #[doc = "The load and the store are always sequentially consistent."]
            #[requires(self.0 == *own.ward())]
            #[ensures(
                match (result.0, *result.2) {
                    (Ok(v), Ok(acq_view)) =>
                        v.deep_model() == current.deep_model() &&
                        Success::Load::load_post(self.0, *own, *sync_view, v, *result.1, acq_view) &&
                        Success::Store::store_post(self.0, *own, *sync_view, new, *result.1 + 1, *rel_view),
                    (Err(v), Err(acq_view)) =>
                        Failure::load_post(self.0, *own, *sync_view, v, *result.1, acq_view),
                    _ => false,
                }
            )]
            fn wrap_compare_exchange_weak<Success: UpdateOrdering, Failure: LoadOrdering>(&self, current: $type, new: $type, mut own : Ghost<&mut Perm<$atomic_type $(< $T >)?>>, mut sync_view: Ghost<&mut SyncView>, rel_view : Ghost<<Success::Store as StoreOrdering>::Rel>) -> (Result<$type, $type>, Snapshot<Timestamp>, Ghost<Result<<Success::Load as LoadOrdering>::Acq, Failure::Acq>>)
            {
                let mut ts: Snapshot<Timestamp> = snapshot!(0);
                let mut acq_view_opt = ghost!(None);
                let f = ghost!(|c : Result<&mut Committer<_, $type, Success::Load, Success::Store>, &Committer<_, $type, Failure, _>>| {
                    match c {
                        Ok(c) => {
                            let acq_view = c.shoot_load(*own, *sync_view);
                            ts = snapshot!(c.timestamp());
                            acq_view_opt = ghost!(Some(Ok(acq_view)));
                            c.shoot_store(*own, *sync_view, *rel_view);
                        },
                        Err(c) => {
                            let acq_view = c.shoot_load(*own, *sync_view);
                            ts = snapshot!(c.timestamp());
                            acq_view_opt = ghost!(Some(Err(acq_view)));
                        }
                    }
                });
                let res = self.0.compare_exchange_weak::<_, Success, Failure>(current, new, f);
                (res, ts, ghost!(acq_view_opt.unwrap()))
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
