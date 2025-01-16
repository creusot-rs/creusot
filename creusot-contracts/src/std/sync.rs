use crate::*;
use ::std::{alloc::Allocator, sync::Arc};

impl<T: DeepModel, A: Allocator> DeepModel for Arc<T, A> {
    type DeepModelTy = T::DeepModelTy;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self.view().deep_model() }
    }
}

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
