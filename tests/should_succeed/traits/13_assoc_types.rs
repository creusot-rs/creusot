extern crate creusot_std;

pub trait Model {
    type ModelTy;

    fn model(self) -> Self::ModelTy;
}

impl<T: Model> Model for &T {
    type ModelTy = T::ModelTy;

    #[allow(unconditional_recursion)]
    fn model(self) -> Self::ModelTy {
        (self).model()
    }
}
