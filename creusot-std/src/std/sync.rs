use crate::prelude::*;
use std::sync::Arc;

#[cfg(creusot)]
use crate::std::ptr::PointerExt as _;

#[cfg(creusot)]
use core::ops::Deref;

#[cfg(feature = "nightly")]
use core::alloc::Allocator;

#[cfg(feature = "sc-drf")]
pub mod atomic_sc;

/// Extension trait for [`Arc`].
pub trait ArcExt {
    /// The `T` in `Arc<T>`
    type Pointee: ?Sized;

    /// Get the underlying raw pointer, in logic.
    ///
    /// Used to specify [`Arc::as_ptr`].
    #[logic]
    fn as_ptr_logic(self) -> *const Self::Pointee;
}
#[cfg(feature = "nightly")]
impl<T: ?Sized, A: Allocator> ArcExt for Arc<T, A> {
    type Pointee = T;
    #[logic(opaque)]
    fn as_ptr_logic(self) -> *const T {
        dead
    }
}

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

            impl<T, A: Allocator> Arc<T, A> {
                #[check(ghost)]
                #[ensures(result == this.as_ptr_logic())]
                #[ensures(!result.is_null_logic())]
                fn as_ptr(this: &Arc<T, A>) -> *const T;

                #[check(terminates)] // Not ghost, as this would allow deducing that there is a finite number of possible `Arc`s.
                #[ensures(result == (this.as_ptr_logic().deep_model() == other.as_ptr_logic().deep_model()))]
                #[ensures(result ==> this@ == other@)]
                fn ptr_eq(this: &Arc<T, A>, other: &Arc<T, A>) -> bool;
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
        #[ensures(result == *self)]
        fn clone(&self) -> Arc<T, A>;
    }

    impl<T: ?Sized, A: Allocator> Deref for Arc<T, A> {
        #[check(ghost)]
        #[ensures(*result == *(*self)@)]
        fn deref(&self) -> &T { self.as_ref() }
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
