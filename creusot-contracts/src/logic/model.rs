use crate as creusot_contracts;
use creusot_contracts_proc::*;

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

impl<T> Model for [T] {
    type ModelTy = crate::Seq<T>;

    #[logic]
    #[trusted]
    #[creusot::builtins = "prelude.Prelude.id"]
    fn model(self) -> Self::ModelTy {
        pearlite! { absurd }
    }
}

impl<T, const N: usize> Model for [T; N] {
    type ModelTy = crate::Seq<T>;

    #[logic]
    #[trusted]
    #[creusot::builtins = "prelude.Prelude.id"]
    fn model(self) -> Self::ModelTy {
        pearlite! { absurd }
    }
}
