use crate::{
    ghost::{
        Committer, FnGhost,
        perm::{Container, Perm},
    },
    prelude::*,
};
#[cfg(feature = "nightly")]
use core::alloc::Allocator;
use std::sync::Arc;

#[cfg(feature = "nightly")]
impl<T: DeepModel + ?Sized, A: Allocator> DeepModel for Arc<T, A> {
    type DeepModelTy = T::DeepModelTy;
    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { *self.view().deep_model() }
    }
}

#[cfg(feature = "nightly")]
impl<T: ?Sized, A: Allocator> View for Arc<T, A> {
    type ViewTy = Box<T>;
    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

extern_spec! {
    mod std {
        mod sync {
            impl<T> Arc<T> {
                #[check(ghost)]
                #[ensures(*result@ == value)]
                fn new(value: T) -> Self;
            }

            impl<T, A: Allocator> AsRef for Arc<T, A> {
                #[check(ghost)]
                #[ensures(*result == *(*self)@)]
                fn as_ref(&self) -> &T;
            }
        }
    }

    impl<T: ?Sized, A: Allocator + Clone> Clone for Arc<T, A> {
        #[check(ghost)]
        #[ensures(result@ == (*self)@)]
        fn clone(&self) -> Arc<T, A>;
    }
}

/// Dummy impls that don't use the unstable trait Allocator
#[cfg(not(feature = "nightly"))]
impl<T: DeepModel> DeepModel for Arc<T> {
    type DeepModelTy = T::DeepModelTy;
}

#[cfg(not(feature = "nightly"))]
impl<T> View for Arc<T> {
    type ViewTy = T;
}

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
    #[requires(forall<c: &mut Committer> !c.shot() ==> c.ward() == *self ==> c.new_value() == val + c.old_value() ==>
        f.precondition((c,)) &&
        (forall<r> f.postcondition_once((c,), r) ==> (^c).shot())
    )]
    #[ensures(exists<c: &mut Committer>
        !c.shot() && c.ward() == *self && c.new_value() == val + c.old_value() &&
        c.old_value() == result.0 &&
        f.postcondition_once((c,), *(result.1))
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn fetch_add<'a, A, F>(&'a self, val: i32, f: Ghost<F>) -> (i32, Ghost<A>)
    where
        F: FnGhost + FnOnce(&'a mut Committer) -> A,
    {
        let res = self.0.fetch_add(val, std::sync::atomic::Ordering::SeqCst);
        (res, Ghost::conjure())
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::store`].
    ///
    /// The store is always sequentially consistent.
    #[requires(forall<c: &mut Committer> !c.shot() ==> c.ward() == *self ==> c.new_value() == val ==>
        f.precondition((c,)) &&
        (forall<r> f.postcondition_once((c,), r) ==> (^c).shot())
    )]
    #[ensures(exists<c: &mut Committer>
        !c.shot() && c.ward() == *self && c.new_value() == val &&
        f.postcondition_once((c,), *result)
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn store<'a, A, F>(&'a self, val: i32, f: Ghost<F>) -> Ghost<A>
    where
        F: FnGhost + FnOnce(&'a mut Committer) -> A,
    {
        self.0.store(val, std::sync::atomic::Ordering::SeqCst);
        Ghost::conjure()
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::into_inner`].
    #[requires(self == *own.ward())]
    #[ensures(result == *own.val())]
    #[trusted]
    pub fn into_inner(self, own: Ghost<Box<Perm<AtomicI32>>>) -> i32 {
        self.0.into_inner()
    }
}
