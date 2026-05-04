use crate::{
    ghost::{
        FnGhost,
        perm::{Perm, PermTarget},
    },
    logic::FMap,
    prelude::*,
    std::sync::{
        committer::Committer,
        view::{HasTimestamp, SyncView, Timestamp},
    },
};

/// Creusot wrapper around [`std::sync::atomic::Ordering`].
#[allow(non_snake_case)]
pub mod Ordering {
    use std::sync::atomic;

    pub trait Ordering {
        const ORDERING: atomic::Ordering;

        type Load: Ordering;
        type Store: Ordering;
    }

    pub struct None;

    macro_rules! impl_ordering {
        ( $order:ident, load = $load:ident, store = $store:ident ) => {
            pub struct $order;

            impl Ordering for $order {
                const ORDERING: atomic::Ordering = atomic::Ordering::$order;

                type Load = $load;
                type Store = $store;
            }
        };
    }

    impl_ordering!(Relaxed, load = Relaxed, store = Relaxed);
    impl_ordering!(Acquire, load = Acquire, store = Relaxed);
    impl_ordering!(Release, load = Relaxed, store = Release);
    impl_ordering!(AcqRel, load = Acquire, store = Release);
    impl_ordering!(SeqCst, load = SeqCst, store = SeqCst);
}

use Ordering::Ordering as _;

macro_rules! impl_atomic {
    ($( ($type:ty, $atomic_type:ident $(< $T:ident >)?) ),+) => { $(

        #[doc = concat!("Creusot wrapper around [`std::sync::atomic::", stringify!($atomic_type), "`].")]
        pub struct $atomic_type $(< $T >)?(::std::sync::atomic::$atomic_type $(< $T >)?);

        impl $(< $T >)? PermTarget for $atomic_type $(< $T >)? {
            type Value = FMap<Timestamp, ($type, SyncView)>;
            type PermPayload = ();
        }

        impl $(< $T >)? HasTimestamp for $atomic_type $(< $T >)? {
            #[logic(opaque)]
            fn get_timestamp(self, _: SyncView) -> Timestamp {
                dead
            }

            #[logic(law)]
            #[requires(x <= y)]
            #[ensures(self.get_timestamp(x) <= self.get_timestamp(y))]
            #[trusted]
            fn get_timestamp_monotonic(self, x: SyncView, y: SyncView) {}
        }

        impl $(< $T >)? $atomic_type $(< $T >)? {
            #[ensures(*result.1.val() == FMap::singleton(result.0.get_timestamp(^sync_view), (val, **sync_view)))]
            #[ensures(*result.1.ward() == result.0)]
            #[inline(always)]
            #[trusted]
            #[check(terminates)]
            #[allow(unused_variables)]
            pub fn new(val: $type, sync_view: Ghost<&mut SyncView>) -> (Self, Ghost<Perm<$atomic_type $(< $T >)?>>) {
                (Self(std::sync::atomic::$atomic_type::new(val)), Ghost::conjure())
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::into_inner`].")]
            #[requires(self == *own.ward())]
            #[ensures(match own.val().get(*result.1) { Some((v, _)) => result.0 == v, None => false })]
            #[ensures(self.get_timestamp(^sync_view) == *result.1)]
            #[ensures(forall<t> match own.val().get(t) {
                Some((_, view)) => t <= *result.1 && view <= ^sync_view,
                None => true
            })]
            #[inline(always)]
            #[trusted]
            #[allow(unused_variables)]
            pub fn into_inner(self, own: Ghost<Perm<$atomic_type $(< $T >)?>>, sync_view: Ghost<&mut SyncView>) -> ($type, Ghost<Timestamp>) {
                (self.0.into_inner(), Ghost::conjure())
            }


            #[doc = "Clear the old unusable history, thanks to the full ownership of the atomic."]
            #[requires(*self == *own.ward())]
            #[ensures(match (*own).val().get(*result) {
                Some((v, _)) => *(^own).val() == FMap::singleton(*result, (v, **sync_view)),
                None => false
            })]
            #[ensures(self.get_timestamp(^sync_view) == *result)]
            #[ensures(forall<t> match own.val().get(t) {
                Some((_, view)) => t <= *result && view <= ^sync_view ,
                None => true
            })]
            #[ensures(*self == ^self)]
            #[inline(always)]
            #[trusted]
            #[check(terminates)]
            #[allow(unused_variables)]
            pub fn refresh(&mut self, own: Ghost<&mut Perm<$atomic_type $(< $T >)?>>, sync_view: Ghost<&mut SyncView>) -> Ghost<Timestamp> {
                 Ghost::conjure()
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::compare_exchange`].")]
            #[doc = ""]
            #[doc = "The load and the store are always sequentially consistent."]
            #[requires(Success::ORDERING != Ordering::SeqCst::ORDERING)]
            #[requires(Failure::ORDERING == Ordering::Acquire::ORDERING || Failure::ORDERING == Ordering::Relaxed::ORDERING)]
            #[requires(forall<c: &mut Committer<Self, $type, _, _>>
                !c.shot_store() ==> c.ward() == *self ==>
                c.val_load().deep_model() == current.deep_model() ==>
                c.val_store() == new ==>
                f.precondition((Ok(c),)) && (f.postcondition_once((Ok(c),), ()) ==> (^c).shot_store())
            )]
            #[requires(forall<c: &Committer<Self, $type, _, _>>
                !c.shot_store() ==> c.ward() == *self ==>
                // NOTE: This following line is not present for `weak`
                c.val_load().deep_model() != current.deep_model() ==>
                f.precondition((Err(c),))
            )]
            #[ensures(
                match result {
                    Ok(result) => {
                        exists<c: &mut Committer<Self, $type, _, _>>
                            !c.shot_store() && c.ward() == *self &&
                            c.val_load().deep_model() == current.deep_model() &&
                            c.val_store() == new &&
                            result == c.val_load() &&
                            f.postcondition_once((Ok(c),), ())
                    },
                    Err(result) => {
                       exists<c: &Committer<Self, $type, _, _>>
                            !c.shot_store() && c.ward() == *self &&
                            // NOTE: This following line is not present for `weak`
                            c.val_load().deep_model() != current.deep_model() &&
                            result == c.val_load() &&
                            f.postcondition_once((Err(c),), ())
                    }
                }
            )]
            #[inline(always)]
            #[trusted]
            #[allow(unused_variables)]
            pub fn compare_exchange<F, Success: Ordering::Ordering, Failure: Ordering::Ordering>(&self, current: $type, new: $type, f: Ghost<F>) -> Result<$type, $type>
            where
                F: FnGhost + FnOnce(Result<
                    &mut Committer<Self, $type, Success::Load, Success::Store>,
                    &Committer<Self, $type, Failure, Ordering::None>
                >,
            )
            {
                self.0.compare_exchange(current, new, Success::ORDERING, Failure::ORDERING)
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::compare_exchange_weak`].")]
            #[doc = ""]
            #[doc = "The load and the store are always sequentially consistent."]
            #[requires(Success::ORDERING != Ordering::SeqCst::ORDERING)] // TODO: [VL] Shouldn't it be enforce by a sc-drf flag instead?
            #[requires(Failure::ORDERING == Ordering::Acquire::ORDERING || Failure::ORDERING == Ordering::Relaxed::ORDERING)]
            #[requires(forall<c: &mut Committer<Self, $type, _, _>> // TODO: [VL] Wrong permission here (Success == Ordering::RelAcq)
                !c.shot_store() ==> c.ward() == *self ==>
                c.val_load().deep_model() == current.deep_model() ==>
                c.val_store() == new ==>
                f.precondition((Ok(c),)) && (f.postcondition_once((Ok(c),), ()) ==> (^c).shot_store())
            )]
            #[requires(forall<c: &Committer<Self, $type, _, _>>
                !c.shot_store() ==> c.ward() == *self ==>
                f.precondition((Err(c),))
            )]
            #[ensures(
                match result {
                    Ok(result) => {
                        exists<c: &mut Committer<Self, $type, _, _>>
                            !c.shot_store() && c.ward() == *self &&
                            c.val_load().deep_model() == current.deep_model() &&
                            c.val_store() == new &&
                            result == c.val_load() &&
                            f.postcondition_once((Ok(c),), ())
                    },
                    Err(result) => {
                       exists<c: &Committer<Self, $type, _, _>>
                            !c.shot_store() && c.ward() == *self &&
                            result == c.val_load() &&
                            f.postcondition_once((Err(c),), ())
                    }
                }
            )]
            #[inline(always)]
            #[trusted]
            #[allow(unused_variables)]
            pub fn compare_exchange_weak<F, Success: Ordering::Ordering, Failure: Ordering::Ordering>(&self, current: $type, new: $type, f: Ghost<F>) -> Result<$type, $type>
            where
                F: FnGhost + FnOnce(Result<
                    &mut Committer<Self, $type, Success::Load, Success::Store>,
                    &Committer<Self, $type, Failure, Ordering::None>
                >,
            )
            {
                self.0.compare_exchange_weak(current, new, Success::ORDERING, Failure::ORDERING)
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::load`].")]
            #[requires(Load::ORDERING == Ordering::Acquire::ORDERING || Load::ORDERING == Ordering::Relaxed::ORDERING)]
            #[requires(forall<c: &Committer<Self, $type, Load, Ordering::None>>
                !c.shot_store() ==> c.ward() == *self ==> f.precondition((c,))
            )]
            #[ensures(exists<c: &Committer<Self, $type, Load, Ordering::None>>
                !c.shot_store() && c.ward() == *self && c.val_load() == result && f.postcondition_once((c,), ())
            )]
            #[inline(always)]
            #[trusted]
            #[allow(unused_variables)]
            pub fn load<F, Load: Ordering::Ordering>(&self, f: Ghost<F>) -> $type
            where
                F: FnGhost + FnOnce(&Committer<Self, $type, Load, Ordering::None>),
            {
                // TODO: [VL] Do this check inside the macro_rules
                self.0.load(if cfg!(feature = "sc-drf") {
                    Ordering::SeqCst::ORDERING
                } else {
                    Load::ORDERING
                })
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::store`].")]
            #[requires(Store::ORDERING == Ordering::Release::ORDERING || Store::ORDERING == Ordering::Relaxed::ORDERING)]
            #[requires(forall<c: &mut Committer<Self, $type, Ordering::None, Store>>
                !c.shot_store() ==> c.ward() == *self ==> c.val_store() == val ==>
                f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot_store())
            )]
            #[ensures(exists<c: &mut Committer<Self, $type, Ordering::None, Store>>
                !c.shot_store() && c.ward() == *self && c.val_store() == val &&
                f.postcondition_once((c,), ())
            )]
            #[inline(always)]
            #[trusted]
            #[allow(unused_variables)]
            pub fn store<F, Store: Ordering::Ordering>(&self, val: $type, f: Ghost<F>)
            where
                F: FnGhost + FnOnce(&mut Committer<Self, $type, Ordering::None, Store>),
            {
                self.0.store(
                    val,
                    if cfg!(feature = "sc-drf") {
                        Ordering::SeqCst::ORDERING
                    } else {
                        Store::ORDERING
                    },
                )
            }
        }

    )* };
}

macro_rules! impl_atomic_int {
    ($( ($int_type:ty, $atomic_type:ident) ),+) => { $(

        impl_atomic!(($int_type, $atomic_type));

        impl $atomic_type {
            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::fetch_add`].")]
            #[requires(forall<c: &mut Committer<Self, $int_type, Ord::Load, Ord::Store>>
                !c.shot_store() ==> c.ward() == *self ==> c.val_store() == val + c.val_load() ==>
                f.precondition((c,)) && (f.postcondition_once((c,), ()) ==> (^c).shot_store())
            )]
            #[ensures(exists<c: &mut Committer<Self, $int_type, Ord::Load, Ord::Store>>
                !c.shot_store() && c.ward() == *self && c.val_store() == val + c.val_load() &&
                c.val_load() == result && f.postcondition_once((c,), ())
            )]
            #[trusted]
            #[allow(unused_variables)]
            pub fn fetch_add<F, Ord: Ordering::Ordering>(&self, val: $int_type, f: Ghost<F>) -> $int_type
            where
                F: FnGhost + FnOnce(&mut Committer<Self, $int_type, Ord::Load, Ord::Store>),
            {
                self.0.fetch_add(val, Ordering::SeqCst::ORDERING)
            }
        }

    )* };
}

impl_atomic! {
    (bool, AtomicBool),
    (*mut T, AtomicPtr<T>)
}

impl_atomic_int! {
    (i8, AtomicI8),
    (u8, AtomicU8),
    (i16, AtomicI16),
    (u16, AtomicU16),
    (i32, AtomicI32),
    (u32, AtomicU32),
    (i64, AtomicI64),
    (u64, AtomicU64),
    (isize, AtomicIsize),
    (usize, AtomicUsize)
}
