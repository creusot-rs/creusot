extern crate creusot_contracts;

use creusot_contracts::{logic::PartialOrdLogic, *};

extern_spec! {
    impl<U: PartialOrd<U> + DeepModel, T: PartialOrd<T> + DeepModel> PartialOrd for (U, T)
    where U::DeepModelTy: PartialOrdLogic, T::DeepModelTy: PartialOrdLogic
    {
        #[ensures(result == self.deep_model().lt_log(o.deep_model()))]
        fn lt(&self, o: &(U, T)) -> bool;
    }
}

pub fn uses_concrete_instance(x: (u32, u32), y: (u32, u32)) -> bool {
    x < y
}
