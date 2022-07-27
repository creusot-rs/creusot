use crate as creusot_contracts;
use crate::macros::*;
#[cfg(feature = "contracts")]
use std::alloc::Allocator;

pub trait Model {
    type ModelTy;
    #[logic]
    fn model(self) -> Self::ModelTy;
}

impl<T: Model + ?Sized> Model for &T {
    type ModelTy = T::ModelTy;
    #[logic]
    fn model(self) -> Self::ModelTy {
        (*self).model()
    }
}

impl<T: Model + ?Sized> Model for &mut T {
    type ModelTy = T::ModelTy;
    #[logic]
    fn model(self) -> Self::ModelTy {
        (*self).model()
    }
}

#[cfg(feature = "contracts")]
impl<T: Model + ?Sized, A: Allocator> Model for Box<T, A> {
    type ModelTy = T::ModelTy;
    #[logic]
    fn model(self) -> Self::ModelTy {
        (*self).model()
    }
}

impl<T, const N: usize> Model for [T; N] {
    type ModelTy = crate::Seq<T>;

    #[logic]
    #[creusot::builtins = "prelude.Slice.id"]
    fn model(self) -> Self::ModelTy {
        pearlite! { absurd }
    }
}

impl<T: Model, U: Model> Model for (T, U) {
    type ModelTy = (T::ModelTy, U::ModelTy);

    #[logic]
    fn model(self) -> Self::ModelTy {
        pearlite! { (@self.0, @self.1) }
    }
}

impl Model for bool {
    type ModelTy = bool;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self
    }
}

impl<T: Model> Model for Option<T> {
    type ModelTy = Option<T::ModelTy>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        match self {
            Some(t) => Some(t.model()),
            None => None,
        }
    }
}
