use crate::{
    ghost::{Committer, Container, FnGhost, perm::Perm},
    logic::FMap,
    prelude::*,
    view::{HasTimestamp, SyncView, Timestamp},
};

/// Creusot wrapper around [`std::sync::atomic::AtomicI32`]
pub struct AtomicI32(::std::sync::atomic::AtomicI32);

impl Container for AtomicI32 {
    type Value = FMap<Timestamp, (i32, SyncView)>;

    #[logic(open, inline)]
    fn is_disjoint(&self, _: &Self::Value, other: &Self, _: &Self::Value) -> bool {
        // TODO: [VL]
        false
    }
}

impl HasTimestamp for AtomicI32 {
    #[logic(opaque)]
    fn get_timestamp(self, view: SyncView) -> Timestamp {
        dead
    }

    #[logic(law)]
    #[ensures(x.le_log(y) == self.get_timestamp(x).le_log(self.get_timestamp(y)))]
    fn get_timestamp_monotonic(self, x: SyncView, y: SyncView) {}
}

impl AtomicI32 {
    #[trusted]
    #[check(terminates)]
    pub fn new(val: i32) -> (Self, Ghost<Box<Perm<AtomicI32>>>) {
        (Self(std::sync::atomic::AtomicI32::new(val)), Ghost::conjure())
    }

    pub fn store<'a, A, F>(&'a self, val: i32, f: Ghost<F>) -> Ghost<A>
    where
        F: FnGhost + FnOnce(&'a mut Committer<Self>) -> A,
    {
        self.0.store(val, ::std::sync::atomic::Ordering::Release);
        Ghost::conjure()
    }

    pub fn load<'a, A, F>(&'a self, f: Ghost<F>) -> (i32, Ghost<A>)
    where
        F: FnGhost + FnOnce(&'a mut Committer<Self>) -> A,
    {
        let res = self.0.load(::std::sync::atomic::Ordering::Acquire);
        (res, Ghost::conjure())
    }

    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicI32>>>) -> i32 {
        self.0.into_inner()
    }
}
