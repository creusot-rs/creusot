use crate::{invariant::*, std::alloc::Allocator, *};
pub use ::std::boxed::*;

impl<T: DeepModel + ?Sized, A: Allocator> DeepModel for Box<T, A> {
    type DeepModelTy = Box<T::DeepModelTy>;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        Box::new((*self).deep_model())
    }
}

impl<T: View + ?Sized, A: Allocator> View for Box<T, A> {
    type ViewTy = T::ViewTy;
    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        (*self).view()
    }
}

impl<T: ?Sized, A: Allocator> Invariant for Box<T, A> {
    #[predicate(prophetic)]
    #[open]
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
                #[pure]
                #[ensures(*result == val)]
                fn new(val: T) -> Self;
            }

            impl<T, A: Allocator> Box<T, A> {
                #[pure]
                #[ensures(**self == *result)]
                #[ensures(*^self == ^result)]
                fn as_mut(&mut self) -> &mut T;

                #[pure]
                #[ensures(**self == *result)]
                fn as_ref(&self) -> &T;
            }
        }
    }
}
