use crate::*;
use ::std::{alloc::Allocator, rc::Rc};

impl<T: DeepModel, A: Allocator> DeepModel for Rc<T, A> {
    type DeepModelTy = T::DeepModelTy;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { self.view().deep_model() }
    }
}

impl<T, A: Allocator> View for Rc<T, A> {
    type ViewTy = T;
    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

extern_spec! {
    mod std {
        mod rc {
            impl<T> Rc<T> {
                #[ensures(result@ == value)]
                fn new(value: T) -> Self;
            }

            impl<T, A: Allocator> AsRef for Rc<T, A> {
                #[ensures(*result == (*self)@)]
                fn as_ref(&self) -> &T;
            }
        }
    }
}
