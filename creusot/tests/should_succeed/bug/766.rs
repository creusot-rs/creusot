extern crate creusot_contracts;
use creusot_contracts::{logic::FMap, *};

trait Trait<T: DeepModel, U: DeepModel>:
    DeepModel<DeepModelTy = FMap<T::DeepModelTy, U::DeepModelTy>>
{
    #[ensures(self.deep_model() == self.deep_model())]
    fn f(&mut self);

    fn goo(&mut self) {
        self.f()
    }
}
