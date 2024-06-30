use crate::{std::alloc::Allocator, *};
pub use ::std::boxed::*;

#[cfg(creusot)]
impl<T: EqModel + ?Sized, A: Allocator> EqModel for Box<T, A> {
    type EqModelTy = Box<T::EqModelTy>;
    #[logic]
    #[open]
    fn eq_model(self) -> Self::EqModelTy {
        Box::new((*self).eq_model())
    }
}

#[cfg(creusot)]
impl<T: View + ?Sized, A: Allocator> View for Box<T, A> {
    type ViewTy = T::ViewTy;
    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        (*self).view()
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
