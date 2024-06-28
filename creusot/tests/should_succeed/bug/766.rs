extern crate creusot_contracts;
use creusot_contracts::{logic::FMap, *};

pub trait Trait<T: EqModel, U: EqModel>:
    EqModel<EqModelTy = FMap<T::EqModelTy, U::EqModelTy>>
{
    #[ensures(self.eq_model() == self.eq_model())]
    fn f(&mut self);

    fn goo(&mut self) {
        self.f()
    }
}
