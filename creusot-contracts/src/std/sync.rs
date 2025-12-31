use crate::{
    ghost::{Committer, FnGhost},
    prelude::*,
};
#[cfg(feature = "nightly")]
use std::alloc::Allocator;
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

impl AtomicI32 {
    /// Wrapper for [`std::sync::atomic::AtomicI32::fetch_add`].
    ///
    /// The fetch and the store are always sequentially consistent.
    // TODO: Handle overflow wrapping
    #[requires(forall<c: &mut Committer> !c.shot() ==> c.tied() == *self ==> (^c).value()@ == val@ + (*c).value()@ ==>
        f.precondition((c,)) &&
        (forall<r> f.postcondition_once((c,), r) ==> (^c).shot())
    )]
    #[ensures(exists<c: &mut Committer>
        !c.shot() && c.tied() == *self && (^c).value()@ == val@ + (*c).value()@ &&
        f.postcondition_once((c,), *result)
    )]
    #[trusted]
    #[allow(unused_variables)]
    pub fn fetch_add<'a, A, F>(&'a self, val: i32, f: Ghost<F>) -> Ghost<A>
    where
        F: FnGhost + FnOnce(&'a mut Committer) -> A,
    {
        self.0.fetch_add(val, std::sync::atomic::Ordering::SeqCst);
        Ghost::conjure()
    }

    /// Wrapper for [`std::sync::atomic::AtomicI32::store`].
    ///
    /// The store is always sequentially consistent.
    #[requires(forall<c: &mut Committer> !c.shot() ==> c.tied() == *self ==> (^c).value() == val ==>
        f.precondition((c,)) &&
        (forall<r> f.postcondition_once((c,), r) ==> (^c).shot())
    )]
    #[ensures(exists<c: &mut Committer>
        !c.shot() && c.tied() == *self && (^c).value() == val &&
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
    #[requires(self == own.tied())]
    #[ensures(result == own.val())]
    #[trusted]
    pub fn into_inner(self, own: Ghost<AtomicI32Own>) -> i32 {
        self.0.into_inner()
    }
}

/// Ownership for a [`AtomicI32`].
#[opaque]
pub struct AtomicI32Own;

impl AtomicI32Own {
    /// The atomic which this [`AtomicI32Own`] holds the ownership for
    #[logic(opaque)]
    pub fn tied(self) -> AtomicI32 {
        dead
    }

    /// Value currently contained in the atomic
    #[logic(opaque)]
    pub fn val(self) -> i32 {
        dead
    }

    #[ensures(result.1.val() == val)]
    #[ensures(result.1.tied() == result.0)]
    #[trusted]
    pub fn new(val: i32) -> (AtomicI32, Ghost<AtomicI32Own>) {
        (AtomicI32(std::sync::atomic::AtomicI32::new(val)), Ghost::conjure())
    }
}
