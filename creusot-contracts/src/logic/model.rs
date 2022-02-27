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
    fn model(self) -> Self::ModelTy {
        id(self)
    }
}

#[creusot::builtins = "prelude.Prelude.id"]
fn id<T>(x: [T]) -> crate::Seq<T> {
    std::process::abort()
}
