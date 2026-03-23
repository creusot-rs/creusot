#[cfg(creusot)]
use crate::sync_view::Objective;

use crate::{
    ghost::{Container, FnGhost, perm::Perm},
    logic::FMap,
    prelude::*,
    sync_view::{HasTimestamp, SyncView, Timestamp, View},
};
use core::marker::PhantomData;

macro_rules! impl_atomic {
    ($( ($type:ty, $atomic_type:ident $(< $T:ident >)?) ),+) => { $(

        #[doc = concat!("Creusot wrapper around [`std::sync::atomic::", stringify!($atomic_type), "`].")]
        pub struct $atomic_type $(< $T >)?(::std::sync::atomic::$atomic_type $(< $T >)?);

        unsafe impl $(< $T >)? Send for Perm<$atomic_type $(< $T >)?> {}
        unsafe impl $(< $T >)? Sync for Perm<$atomic_type $(< $T >)?> {}

        #[cfg(creusot)]
        #[trusted]
        impl $(< $T >)? Objective for Perm<$atomic_type $(< $T >)?> {}

        impl $(< $T >)? Container for $atomic_type $(< $T >)? {
            type Value = FMap<Timestamp, ($type, View)>;

            #[logic(open, inline)]
            fn is_disjoint(&self, _: &Self::Value, other: &Self, _: &Self::Value) -> bool {
                self != other
            }
        }

        impl $(< $T >)? HasTimestamp for $atomic_type $(< $T >)? {
            #[logic(opaque)]
            fn get_timestamp(self, _: View) -> Timestamp {
                dead
            }

            #[logic(law)]
            #[requires(x.le_log(y))]
            #[ensures(self.get_timestamp(x).le_log(self.get_timestamp(y)))]
            #[trusted]
            fn get_timestamp_monotonic(self, x: View, y: View) {}
        }

        impl $(< $T >)? $atomic_type $(< $T >)? {
            #[ensures(*result.1.val() == FMap::singleton(result.0.get_timestamp((^sync_view).view()), (val, (**sync_view).view())))]
            #[ensures(*result.1.ward() == result.0)]
            #[trusted]
            #[check(terminates)]
            #[allow(unused_variables)]
            pub fn new(val: $type, sync_view: Ghost<&mut SyncView>) -> (Self, Ghost<Box<Perm<$atomic_type $(< $T >)?>>>) {
                (Self(std::sync::atomic::$atomic_type::new(val)), Ghost::conjure())
            }

            // TODO: [VL] into_inner

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::load`].")]
            #[requires(forall<c: &LoadCommitter<$type, Self>> c.ward() == *self ==> f.precondition((c,)))]
            #[ensures(exists<c: &LoadCommitter<$type, Self>>
                c.ward() == *self && c.val() == result && f.postcondition_once((c,), ())
            )]
            #[trusted]
            #[allow(unused_variables)]
            pub fn load<F>(&self, f: Ghost<F>) -> $type
            where
                F: FnGhost + FnOnce(&LoadCommitter<$type, Self>),
            {
                self.0.load(if cfg!(feature = "sc-drf") {
                    ::std::sync::atomic::Ordering::SeqCst
                } else {
                    ::std::sync::atomic::Ordering::Acquire
                })
            }

            #[doc = concat!("Wrapper for [`std::sync::atomic::", stringify!($atomic_type), "::store`].")]
            #[requires(forall<c: &mut StoreCommitter<$type, Self>> !c.shot() ==> c.ward() == *self ==> c.val() == val ==>
                f.precondition((c,)) && f.postcondition_once((c,), ()) ==> (^c).shot()
            )]
            #[ensures(exists<c: &mut StoreCommitter<$type, Self>>
                !c.shot() && c.ward() == *self && c.val() == val &&
                f.postcondition_once((c,), ())
            )]
            #[trusted]
            #[allow(unused_variables)]
            pub fn store<F>(&self, val: $type, f: Ghost<F>)
            where
                F: FnGhost + FnOnce(&mut StoreCommitter<$type, Self>),
            {
                self.0.store(
                    val,
                    if cfg!(feature = "sc-drf") {
                        ::std::sync::atomic::Ordering::SeqCst
                    } else {
                        ::std::sync::atomic::Ordering::Release
                    },
                )
            }
        }

    )* };
}

macro_rules! impl_atomic_int {
    ($( ($int_type:ty, $atomic_type:ident) ),+) => { $(

        impl_atomic!(($int_type, $atomic_type));

        // Nothing yet.

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

/// Wrapper around a single atomic load operation, where multiple ghost steps
/// can be performed.
///
/// Note: this committer has no observable effect on ghost ressources. Thus, it is optional to shoot
/// it, and nothing prevent the user from shooting it several times.
// This trick is correct for SC accesses under SC-DRF, and for Rel/Acq/Rlx and Rlx accesses, but
// perhaps not for C20's SC accesses.
#[opaque]
pub struct LoadCommitter<T, C: Container<Value = FMap<Timestamp, (T, View)>>>(PhantomData<(T, C)>);

impl<T, C: Container<Value = FMap<Timestamp, (T, View)>> + HasTimestamp> LoadCommitter<T, C> {
    /// Identity of the committer
    ///
    /// This is used so that we can only use the committer with the right [`AtomicOwn`].
    #[logic(opaque)]
    pub fn ward(self) -> C {
        dead
    }

    /// Value held by the [`AtomicOwn`].
    #[logic(opaque)]
    pub fn val(self) -> T {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code.
    #[requires(self.ward() == *own.ward())]
    #[ensures(((*sync_view).view()).le_log((^sync_view).view()))]
    #[ensures(self.ward().get_timestamp((*sync_view).view()) <= result)]
    #[ensures(result <= self.ward().get_timestamp((^sync_view).view()))]
    #[ensures(match own.val().get(result) {
        Some((v, v_view)) => v == self.val() && v_view.le_log((^sync_view).view()),
        None => false
    })]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&self, own: &Perm<C>, sync_view: &mut SyncView) -> Timestamp {
        panic!("Should not be called outside ghost code")
    }
}

/// Wrapper around a single atomic operation, where multiple ghost steps can be
/// performed.
#[opaque]
pub struct StoreCommitter<T, C: Container<Value = FMap<Timestamp, (T, View)>>>(PhantomData<(T, C)>);

impl<T, C: Container<Value = FMap<Timestamp, (T, View)>> + HasTimestamp> StoreCommitter<T, C> {
    /// Status of the committer
    #[logic(opaque)]
    pub fn shot(self) -> bool {
        dead
    }

    /// Identity of the committer
    ///
    /// This is used so that we can only use the committer with the right [`AtomicOwn`].
    #[logic(opaque)]
    pub fn ward(self) -> C {
        dead
    }

    /// Value held by the [`AtomicOwn`], before the [`shoot`].
    #[logic(opaque)]
    pub fn val(self) -> T {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((^self).shot())]
    #[ensures((*self).ward() == (^self).ward() && (*self).val() == (^self).val())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures(((*sync_view).view()).le_log((^sync_view).view()))]
    #[ensures((*self).ward().get_timestamp((*sync_view).view()) < result)]
    #[ensures(result <= (*self).ward().get_timestamp((^sync_view).view()))]
    #[ensures((*own).val().get(result) == None)]
    #[ensures(*(^own).val() == (*own).val().insert(result, ((*self).val(), (*sync_view).view())))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &mut Perm<C>, sync_view: &mut SyncView) -> Timestamp {
        panic!("Should not be called outside ghost code")
    }
}
