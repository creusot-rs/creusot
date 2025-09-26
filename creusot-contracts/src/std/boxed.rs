use crate::{invariant::*, *};
#[cfg(feature = "nightly")]
use ::std::alloc::Allocator;
pub use ::std::boxed::*;

#[cfg(feature = "nightly")]
impl<T: DeepModel + ?Sized, A: Allocator> DeepModel for Box<T, A> {
    type DeepModelTy = Box<T::DeepModelTy>;
    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        Box::new((*self).deep_model())
    }
}

#[cfg(feature = "nightly")]
impl<T: View + ?Sized, A: Allocator> View for Box<T, A> {
    type ViewTy = T::ViewTy;
    #[logic(open, inline)]
    fn view(self) -> Self::ViewTy {
        (*self).view()
    }
}

#[cfg(feature = "nightly")]
impl<T: ?Sized, A: Allocator> Invariant for Box<T, A> {
    #[logic(open, prophetic)]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        inv(*self)
    }
}

extern_spec! {
    mod std {
        mod boxed {
            impl<T> Box<T> {
                #[check(ghost)]
                #[ensures(*result == val)]
                fn new(val: T) -> Self;
            }

            impl<T, A: Allocator> Box<T, A> {
                #[check(ghost)]
                #[ensures(**self == *result)]
                #[ensures(*^self == ^result)]
                fn as_mut(&mut self) -> &mut T;

                #[check(ghost)]
                #[ensures(**self == *result)]
                fn as_ref(&self) -> &T;

                #[check(ghost)]
                #[ensures(*result == *b)]
                fn leak<'a>(b: Box<T, A>) -> &'a mut T
                where
                    A: 'a;
            }
        }
    }

    impl<T: Clone, A: Allocator + Clone> Clone for Box<T, A> {
        #[ensures(T::clone.postcondition((&**self,), *result))]
        fn clone(&self) -> Box<T, A>;
    }
}

/// Dummy impls that don't use the unstable trait Allocator
#[cfg(not(feature = "nightly"))]
impl<T: DeepModel + ?Sized> DeepModel for Box<T> {
    type DeepModelTy = Box<T::DeepModelTy>;
}

#[cfg(not(feature = "nightly"))]
impl<T: View + ?Sized> View for Box<T> {
    type ViewTy = T::ViewTy;
}

#[cfg(not(feature = "nightly"))]
impl<T: ?Sized> Invariant for Box<T> {}
