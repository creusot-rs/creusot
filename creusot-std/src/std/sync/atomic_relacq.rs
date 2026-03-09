use crate::{
    ghost::{Container, FnGhost, perm::Perm},
    logic::FMap,
    prelude::*,
    view::{HasTimestamp, SyncView, Timestamp},
};
use core::marker::PhantomData;

/// Creusot wrapper around [`std::sync::atomic::AtomicI32`]
pub struct AtomicI32(::std::sync::atomic::AtomicI32);

unsafe impl Send for Perm<AtomicI32> {}
unsafe impl Sync for Perm<AtomicI32> {}

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
    #[ensures(x.le_log(y) == self.get_timestamp(x).le_log(self.get_timestamp(y)))]
    fn get_timestamp_monotonic(self, x: SyncView, y: SyncView) {}
}

impl AtomicI32 {
    #[trusted]
    #[check(terminates)]
    // TODO: Val ? Ward ? Timestamp ?
    pub fn new(val: i32) -> (Self, Ghost<Box<Perm<AtomicI32>>>) {
        (Self(std::sync::atomic::AtomicI32::new(val)), Ghost::conjure())
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::load`].
    #[requires(forall<c: &mut Committer<i32, Self>> !c.shot() ==> c.ward() == *self ==> c.new_value() == c.old_value() ==>
        f.precondition((c,)) && forall<r> f.postcondition_once((c,), r) ==> (^c).shot()
    )]
    #[ensures(exists<c: &mut Committer<i32, Self>>
        !c.shot() && c.ward() == *self && c.new_value() == c.old_value() &&
        // TODO: [VL] Comment accéder à l'historique sans Perm<AtomicI32>
        // (forall<v> c.ward().get(c.timestamp()) == Some(v) && v.0 == result.0) &&
        f.postcondition_once((c,), *(result.1))
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn load<'a, A, F>(&'a self, f: Ghost<F>) -> (i32, Ghost<A>)
    where
        F: FnGhost + FnOnce(&'a mut Committer<i32, Self>) -> A,
    {
        let res = self.0.load(if cfg!(feature = "sc-drf") {
            ::std::sync::atomic::Ordering::SeqCst
        } else {
            ::std::sync::atomic::Ordering::Acquire
        });

        (res, Ghost::conjure())
    }

    #[trusted]
    #[allow(unused_variables)]
    pub fn store<'a, A, F>(&'a self, val: i32, f: Ghost<F>) -> Ghost<A>
    where
        F: FnGhost + FnOnce(&'a mut Committer<i32, Self>) -> A,
    {
        self.0.store(
            val,
            if cfg!(feature = "sc-drf") {
                ::std::sync::atomic::Ordering::SeqCst
            } else {
                ::std::sync::atomic::Ordering::Release
            },
        );

        Ghost::conjure()
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::into_inner`].
    #[trusted]
    #[allow(unused_variables)]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicI32>>>) -> i32 {
        self.0.into_inner()
    }
}

/// Wrapper around a single atomic operation, where multiple ghost steps can be
/// performed.
#[opaque]
pub struct Committer<T, C: Container<Value = FMap<Timestamp, (T, SyncView)>>>(PhantomData<(T, C)>);

impl<T, C: Container<Value = FMap<Timestamp, (T, SyncView)>> + HasTimestamp> Committer<T, C> {
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
    pub fn old_value(self) -> T {
        dead
    }

    /// Value held by the [`AtomicOwn`], after the [`shoot`].
    #[logic(opaque)]
    pub fn new_value(self) -> T {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!self.shot())]
    #[requires(self.ward() == *own.ward())]
    #[ensures((^self).shot())]
    #[ensures((^own).ward() == (*own).ward())]
    #[ensures((*view).le_log(^view))]
    #[ensures((*self).ward().get_timestamp(*view) <= result)]
    #[ensures(result <= (*self).ward().get_timestamp(^view))]
    #[ensures(match (*own).val().get(result) {
        Some((_, v)) => v.le_log(^view),
        None => true
    })]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &mut Perm<C>, view: &mut crate::view::SyncView) -> Timestamp {
        panic!("Should not be called outside ghost code")
    }
}
