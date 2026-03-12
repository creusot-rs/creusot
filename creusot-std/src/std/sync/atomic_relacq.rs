#[cfg(creusot)]
use crate::sync_view::Objective;

use crate::{
    ghost::{Container, FnGhost, perm::Perm},
    logic::FMap,
    prelude::*,
    sync_view::{HasTimestamp, SyncView, Timestamp},
};
use core::marker::PhantomData;

/// Creusot wrapper around [`std::sync::atomic::AtomicI32`]
pub struct AtomicI32(::std::sync::atomic::AtomicI32);

unsafe impl Send for Perm<AtomicI32> {}
unsafe impl Sync for Perm<AtomicI32> {}

#[cfg(creusot)]
#[trusted]
impl Objective for Perm<AtomicI32> {}

impl Container for AtomicI32 {
    type Value = FMap<Timestamp, (i32, SyncView)>;

    #[logic(open, inline)]
    fn is_disjoint(&self, _: &Self::Value, other: &Self, _: &Self::Value) -> bool {
        self != other
    }
}

impl HasTimestamp for AtomicI32 {
    #[logic(opaque)]
    fn get_timestamp(self, _: SyncView) -> Timestamp {
        dead
    }

    #[logic(law)]
    #[requires(x.le_log(y))]
    #[ensures(self.get_timestamp(x).le_log(self.get_timestamp(y)))]
    #[trusted]
    fn get_timestamp_monotonic(self, x: SyncView, y: SyncView) {}
}

impl AtomicI32 {
    #[ensures(*result.1.val() == FMap::singleton(result.0.get_timestamp(^view), (val, **view)))]
    #[ensures(*result.1.ward() == result.0)]
    #[trusted]
    #[check(terminates)]
    #[allow(unused_variables)]
    pub fn new(val: i32, view: Ghost<&mut SyncView>) -> (Self, Ghost<Box<Perm<AtomicI32>>>) {
        (Self(std::sync::atomic::AtomicI32::new(val)), Ghost::conjure())
    }

    // TODO: [VL] into_inner

    /// Wrapper for [`std::sync::atomic::AtomicI32::load`].
    #[requires(forall<c: &LoadCommitter<i32, Self>> c.ward() == *self ==> f.precondition((c,)))]
    #[ensures(exists<c: &LoadCommitter<i32, Self>>
        c.ward() == *self && c.val() == result && f.postcondition_once((c,), ())
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn load<F>(&self, f: Ghost<F>) -> i32
    where
        F: FnGhost + FnOnce(&LoadCommitter<i32, Self>),
    {
        self.0.load(if cfg!(feature = "sc-drf") {
            ::std::sync::atomic::Ordering::SeqCst
        } else {
            ::std::sync::atomic::Ordering::Acquire
        })
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::store`].
    #[requires(forall<c: &mut StoreCommitter<i32, Self>> !c.shot() ==> c.ward() == *self ==> c.val() == val ==>
        f.precondition((c,)) && f.postcondition_once((c,), ()) ==> (^c).shot()
    )]
    #[ensures(exists<c: &mut StoreCommitter<i32, Self>>
        !c.shot() && c.ward() == *self && c.val() == val &&
        f.postcondition_once((c,), ())
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn store<F>(&self, val: i32, f: Ghost<F>)
    where
        F: FnGhost + FnOnce(&mut StoreCommitter<i32, Self>),
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

/// Wrapper around a single atomic load operation, where multiple ghost steps
/// can be performed.
///
/// Note: this committer has no observable effect on ghost ressources. Thus, it is optional to shoot
/// it, and nothing prevent the user from shooting it several times.
// This trick is correct for SC accesses under SC-DRF, and for Rel/Acq/Rlx and Rlx accesses, but
// perhaps not for C20's SC accesses.
#[opaque]
pub struct LoadCommitter<T, C: Container<Value = FMap<Timestamp, (T, SyncView)>>>(
    PhantomData<(T, C)>,
);

impl<T, C: Container<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp> LoadCommitter<T, C> {
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
    #[ensures((*view).le_log(^view))]
    #[ensures(self.ward().get_timestamp(*view) <= result)]
    #[ensures(result <= self.ward().get_timestamp(^view))]
    #[ensures(match own.val().get(result) {
        Some((v, v_view)) => v == self.val() && v_view.le_log(^view),
        None => false
    })]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&self, own: &Perm<C>, view: &mut SyncView) -> Timestamp {
        panic!("Should not be called outside ghost code")
    }
}

/// Wrapper around a single atomic operation, where multiple ghost steps can be
/// performed.
#[opaque]
pub struct StoreCommitter<T, C: Container<Value = FMap<Timestamp, (T, SyncView)>>>(
    PhantomData<(T, C)>,
);

impl<T, C: Container<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp> StoreCommitter<T, C> {
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
    #[ensures((*view).le_log(^view))]
    #[ensures((*self).ward().get_timestamp(*view) < result)]
    #[ensures(result <= (*self).ward().get_timestamp(^view))]
    #[ensures((*own).val().get(result) == None)]
    #[ensures(*(^own).val() == (*own).val().insert(result, ((*self).val(), (*view))))]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &mut Perm<C>, view: &mut SyncView) -> Timestamp {
        panic!("Should not be called outside ghost code")
    }
}
