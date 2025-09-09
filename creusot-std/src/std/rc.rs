use crate::prelude::*;
#[cfg(creusot)]
use crate::std::ptr::PointerExt as _;
use alloc::rc::Rc;
#[cfg(feature = "nightly")]
use alloc::{alloc::Allocator, boxed::Box};
#[cfg(creusot)]
use core::ops::Deref;

/// Extension trait for [`Rc`].
pub trait RcExt {
    /// The `T` in `Rc<T>`
    type Pointee: ?Sized;

    /// Get the underlying raw pointer, in logic.
    ///
    /// Used to specify [`Rc::as_ptr`].
    #[logic]
    fn as_ptr_logic(self) -> *const Self::Pointee;
}

#[cfg(feature = "nightly")]
impl<T: ?Sized, A: Allocator> RcExt for Rc<T, A> {
    type Pointee = T;
    #[logic(opaque)]
    fn as_ptr_logic(self) -> *const T {
        dead
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel + ?Sized, A: Allocator> DeepModel for Rc<T, A> {
    type DeepModelTy = T::DeepModelTy;
    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { *self.view().deep_model() }
    }
}

#[cfg(feature = "nightly")]
impl<T: ?Sized, A: Allocator> View for Rc<T, A> {
    type ViewTy = Box<T>;
    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

extern_spec! {
    mod alloc {
        mod rc {
            impl<T> Rc<T> {
                #[check(ghost)]
                #[ensures(*result@ == value)]
                fn new(value: T) -> Self;
            }

            impl<T, A: Allocator> Rc<T, A> {
                #[check(ghost)]
                #[ensures(result == this.as_ptr_logic())]
                #[ensures(!result.is_null_logic())]
                fn as_ptr(this: &Rc<T, A>) -> *const T;

                #[check(terminates)] // Not ghost, as this would allow deducing that there is a finite number of possible `Rc`s.
                #[ensures(result == (this.as_ptr_logic().deep_model() == other.as_ptr_logic().deep_model()))]
                #[ensures(result ==> this@ == other@)]
                fn ptr_eq(this: &Rc<T, A>, other: &Rc<T, A>) -> bool;
            }


            impl<T, A: Allocator> AsRef for Rc<T, A> {
                #[check(ghost)]
                #[ensures(*result == *(*self)@)]
                fn as_ref(&self) -> &T;
            }
        }
    }

    impl<T: ?Sized, A: Allocator + Clone> Clone for Rc<T, A> {
        #[check(ghost)]
        #[ensures(result == *self)]
        fn clone(&self) -> Rc<T, A>;
    }

    impl<T: ?Sized, A: Allocator> Deref for Rc<T, A> {
        #[check(ghost)]
        #[ensures(*result == *(*self)@)]
        fn deref(&self) -> &T { self.as_ref() }
    }
}

/// Dummy impls that don't use the unstable trait Allocator
#[cfg(not(feature = "nightly"))]
impl<T: DeepModel> DeepModel for Rc<T> {
    type DeepModelTy = T::DeepModelTy;
}

#[cfg(not(feature = "nightly"))]
impl<T> View for Rc<T> {
    type ViewTy = T;
}
