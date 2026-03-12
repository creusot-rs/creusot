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

    /// Wrapper for [`std::sync::atomic::AtomicI32::into_inner`].
    #[requires(self == *own.ward())]
    #[ensures(result == *own.val())]
    #[trusted]
    #[allow(unused_variables)]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicI32>>>) -> i32 {
        self.0.into_inner()
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::load`].
    ///
    /// The load is always sequentially consistent.
    #[requires(forall<c: &mut LoadCommitter<Self>> !c.shot() ==> c.ward() == *self ==>
        f.precondition((c,)) && f.postcondition_once((c,), ()) ==> (^c).shot()
    )]
    #[ensures(exists<c: &mut LoadCommitter<Self>>
        !c.shot() && c.ward() == *self && c.val() == result && f.postcondition_once((c,), ())
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn load<'a, F>(&'a self, f: Ghost<F>) -> i32
    where
        F: FnGhost + FnOnce(&'a mut LoadCommitter<Self>),
    {
        self.0.load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::store`].
    ///
    /// The store is always sequentially consistent.
    #[requires(forall<c: &mut StoreCommitter<Self>> !c.shot() ==> c.ward() == *self ==> c.val() == val ==>
        f.precondition((c,)) && f.postcondition_once((c,), ()) ==> (^c).shot()
    )]
    #[ensures(exists<c: &mut StoreCommitter<Self>>
        !c.shot() && c.ward() == *self && c.val() == val &&
        f.postcondition_once((c,), ())
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn store<'a, F>(&'a self, val: i32, f: Ghost<F>)
    where
        F: FnGhost + FnOnce(&'a mut StoreCommitter<Self>),
    {
        self.0.store(val, std::sync::atomic::Ordering::SeqCst)
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::fetch_add`].
    ///
    /// The load and the store are always sequentially consistent.
    #[requires(forall<c: &mut UpdateCommitter<Self>> !c.shot() ==> c.ward() == *self ==> c.new_val() == val + c.old_val() ==>
        f.precondition((c,)) && f.postcondition_once((c,), ()) ==> (^c).shot()
    )]
    #[ensures(exists<c: &mut UpdateCommitter<Self>>
        !c.shot() && c.ward() == *self && c.new_val() == val + c.old_val() &&
        c.old_val() == result && f.postcondition_once((c,), ())
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn fetch_add<'a, F>(&'a self, val: i32, f: Ghost<F>) -> i32
    where
        F: FnGhost + FnOnce(&'a mut UpdateCommitter<Self>),
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::SeqCst)
    }
}

/// Wrapper around a single atomic load operation, where multiple ghost steps
/// can be performed.
#[opaque]
pub struct LoadCommitter<C: Container<Value: Sized>>(PhantomData<C>);

impl<C: Container<Value: Sized>> LoadCommitter<C> {
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

    /// Value read from the atomic operation.
    #[logic(opaque)]
    pub fn val(self) -> C::Value {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the read on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((^self).shot())]
    #[ensures((*self).val() == *own.val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}

/// Wrapper around a single atomic store operation, where multiple ghost steps
/// can be performed.
#[opaque]
pub struct StoreCommitter<C: Container<Value: Sized>>(PhantomData<C>);

impl<C: Container<Value: Sized>> StoreCommitter<C> {
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

    /// Value written by the atomic operation.
    #[logic(opaque)]
    pub fn val(self) -> C::Value {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the write on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((^self).shot())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures(*(^own).val() == (*self).val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &mut Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}

/// Wrapper around a single atomic update operation, where multiple ghost steps
/// can be performed.
#[opaque]
pub struct UpdateCommitter<C: Container<Value: Sized>>(PhantomData<C>);

impl<C: Container<Value: Sized>> UpdateCommitter<C> {
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
    pub fn old_val(self) -> C::Value {
        dead
    }

    /// Value held by the [`AtomicOwn`], after the [`shoot`].
    #[logic(opaque)]
    pub fn new_val(self) -> C::Value {
        dead
    }

    /// 'Shoot' the committer
    ///
    /// This does the update on the atomic in ghost code, and can only be called once.
    #[requires(!(*self).shot())]
    #[requires(self.ward() == *(*own).ward())]
    #[ensures((^self).shot())]
    #[ensures((*own).ward() == (^own).ward())]
    #[ensures(*(*own).val() == (*self).old_val())]
    #[ensures(*(^own).val() == (*self).new_val())]
    #[check(ghost)]
    #[trusted]
    #[allow(unused_variables)]
    pub fn shoot(&mut self, own: &mut Perm<C>) {
        panic!("Should not be called outside ghost code")
    }
}
