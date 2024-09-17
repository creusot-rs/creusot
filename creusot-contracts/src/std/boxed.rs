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

impl<T: ShallowModel + ?Sized, A: Allocator> ShallowModel for Box<T, A> {
    type ShallowModelTy = T::ShallowModelTy;
    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (*self).shallow_model()
    }
}

impl<T: ?Sized, A: Allocator> Invariant for Box<T, A> {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
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
