use crate::*;
#[cfg(creusot)]
use ::std::alloc::Allocator;
use ::std::sync::Arc;

#[cfg(creusot)]
impl<T: DeepModel, A: Allocator> DeepModel for Arc<T, A> {
    type DeepModelTy = T::DeepModelTy;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self.view().deep_model() }
    }
}

#[cfg(creusot)]
impl<T, A: Allocator> View for Arc<T, A> {
    type ViewTy = T;
    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

extern_spec! {
    mod std {
        mod sync {
            impl<T> Arc<T> {
                #[ensures(result@ == value)]
                fn new(value: T) -> Self;
            }

            impl<T, A: Allocator> AsRef for Arc<T, A> {
                #[ensures(*result == (*self)@)]
                fn as_ref(&self) -> &T;
            }
        }
    }
}

#[cfg(not(creusot))]
impl<T: DeepModel> DeepModel for Arc<T> {
    type DeepModelTy = T::DeepModelTy;
}

#[cfg(not(creusot))]
impl<T> View for Arc<T> {
    type ViewTy = T;
}
