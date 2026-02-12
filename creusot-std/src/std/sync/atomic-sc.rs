use crate::{
    ghost::{Committer, Container, FnGhost, perm::Perm},
    prelude::*,
};

/// Creusot wrapper around [`std::sync::atomic::AtomicI32`]
pub struct AtomicI32(::std::sync::atomic::AtomicI32);

impl Container for AtomicI32 {
    type Value = i32;

    #[logic(open, inline)]
    fn is_disjoint(&self, _: &Self::Value, other: &Self, _: &Self::Value) -> bool {
        self != other
    }
}

impl AtomicI32 {
    #[ensures(*result.1.val() == val)]
    #[ensures(*result.1.ward() == result.0)]
    #[trusted]
    #[check(terminates)]
    pub fn new(val: i32) -> (Self, Ghost<Box<Perm<AtomicI32>>>) {
        (Self(std::sync::atomic::AtomicI32::new(val)), Ghost::conjure())
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::fetch_add`].
    ///
    /// The fetch and the store are always sequentially consistent.
    #[requires(forall<c: &mut Committer<Self>> !c.shot() ==> c.ward() == *self ==> c.new_value() == val + c.old_value() ==>
        f.precondition((c,)) && forall<r> f.postcondition_once((c,), r) ==> (^c).shot()
    )]
    #[ensures(exists<c: &mut Committer<Self>>
        !c.shot() && c.ward() == *self && c.new_value() == val + c.old_value() &&
        c.old_value() == result.0 && f.postcondition_once((c,), *(result.1))
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn fetch_add<'a, A, F>(&'a self, val: i32, f: Ghost<F>) -> (i32, Ghost<A>)
    where
        F: FnGhost + FnOnce(&'a mut Committer<Self>) -> A,
    {
        let res = self.0.fetch_add(val, std::sync::atomic::Ordering::SeqCst);
        (res, Ghost::conjure())
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::store`].
    ///
    /// The store is always sequentially consistent.
    #[requires(forall<c: &mut Committer<Self>> !c.shot() ==> c.ward() == *self ==> c.new_value() == val ==>
        f.precondition((c,)) && (forall<r> f.postcondition_once((c,), r) ==> (^c).shot())
    )]
    #[ensures(exists<c: &mut Committer<Self>>
        !c.shot() && c.ward() == *self && c.new_value() == val &&
        f.postcondition_once((c,), *result)
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn store<'a, A, F>(&'a self, val: i32, f: Ghost<F>) -> Ghost<A>
    where
        F: FnGhost + FnOnce(&'a mut Committer<Self>) -> A,
    {
        self.0.store(val, std::sync::atomic::Ordering::SeqCst);
        Ghost::conjure()
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::into_inner`].
    #[allow(unused_variables)]
    #[requires(self == *own.ward())]
    #[ensures(result == *own.val())]
    #[trusted]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicI32>>>) -> i32 {
        self.0.into_inner()
    }
}
