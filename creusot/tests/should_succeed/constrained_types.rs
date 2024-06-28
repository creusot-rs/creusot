extern crate creusot_contracts;

use creusot_contracts::{logic::OrdLogic, *};

extern_spec! {
    impl<U: PartialOrd<U> + EqModel, T: PartialOrd<T> + EqModel> PartialOrd for (U, T)
    where U::EqModelTy: OrdLogic, T::EqModelTy: OrdLogic
    {
        #[ensures(result == self.eq_model().lt_log(o.eq_model()))]
        fn lt(&self, o: &(U, T)) -> bool;
    }
}

pub fn uses_concrete_instance(x: (u32, u32), y: (u32, u32)) -> bool {
    x < y
}
