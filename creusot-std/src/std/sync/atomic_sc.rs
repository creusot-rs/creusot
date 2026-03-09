use crate::{
    ghost::{Container, FnGhost, perm::Perm},
    prelude::*,
};
use core::marker::PhantomData;

/// Creusot wrapper around [`std::sync::atomic::AtomicI32`]
pub struct AtomicI32(::std::sync::atomic::AtomicI32);

unsafe impl Send for Perm<AtomicI32> {}
unsafe impl Sync for Perm<AtomicI32> {}

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
    /// The load and the store are always sequentially consistent.
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

    /// Wrapper for [`std::sync::atomic::AtomicI32::load`].
    ///
    /// The load is always sequentially consistent.
    #[requires(forall<c: &mut Committer<Self>> !c.shot() ==> c.ward() == *self ==> c.new_value() == c.old_value() ==>
        f.precondition((c,)) && forall<r> f.postcondition_once((c,), r) ==> (^c).shot()
    )]
    #[ensures(exists<c: &mut Committer<Self>>
        !c.shot() && c.ward() == *self && c.new_value() == c.old_value() &&
        c.new_value() == result.0 && f.postcondition_once((c,), *(result.1))
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn load<'a, A, F>(&'a self, f: Ghost<F>) -> (i32, Ghost<A>)
    where
        F: FnGhost + FnOnce(&'a mut Committer<Self>) -> A,
    {
        let res = self.0.load(std::sync::atomic::Ordering::SeqCst);
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
    #[requires(self == *own.ward())]
    #[ensures(result == *own.val())]
    #[trusted]
    #[allow(unused_variables)]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicI32>>>) -> i32 {
        self.0.into_inner()
    }
}

/// Wrapper around a single atomic operation, where multiple ghost steps can be
/// performed.
#[opaque]
pub struct Committer<C: Container<Value: Sized>>(PhantomData<C>);

impl<C: Container<Value: Sized>> Committer<C> {
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
    pub fn old_value(self) -> C::Value {
        dead
    }

    /// Value held by the [`AtomicOwn`], after the [`shoot`].
    #[logic(opaque)]
    pub fn new_value(self) -> C::Value {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!self.shot())]
    #[requires(self.ward() == *own.ward())]
    #[ensures((^self).shot())]
    #[ensures((^own).ward() == (*own).ward())]
    #[ensures(*(*own).val() == (*self).old_value())]
    #[ensures(*(^own).val() == (*self).new_value())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &mut Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}
