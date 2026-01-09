extern crate creusot_std;
use creusot_std::{logic::FMap, prelude::*};

pub trait Trait<T: DeepModel, U: DeepModel>:
    DeepModel<DeepModelTy = FMap<T::DeepModelTy, U::DeepModelTy>>
{
    #[ensures(self.deep_model() == self.deep_model())]
    fn f(&mut self);

    fn goo(&mut self) {
        self.f()
    }
}
