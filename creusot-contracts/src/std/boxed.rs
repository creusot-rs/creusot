use crate::{std::alloc::Allocator, *};
pub use ::std::boxed::*;

#[cfg(creusot)]
impl<T: DeepModel + ?Sized, A: Allocator> DeepModel for Box<T, A> {
    type DeepModelTy = Box<T::DeepModelTy>;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        Box::new((*self).deep_model())
    }
}

#[cfg(creusot)]
impl<T: ShallowModel + ?Sized, A: Allocator> ShallowModel for Box<T, A> {
    type ShallowModelTy = T::ShallowModelTy;
    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (*self).shallow_model()
    }
}

extern_spec! {
    mod std {
        mod boxed {
            impl<T> Box<T> {
                #[ensures(*result == val)]
                fn new(val: T) -> Self;
            }

            impl<T, A: Allocator> Box<T, A> {
                #[ensures(**self == *result)]
                #[ensures(*^self == ^result)]
                fn as_mut(&mut self) -> &mut T;

                #[ensures(**self == *result)]
                fn as_ref(&self) -> &T;
            }
        }
    }
}
