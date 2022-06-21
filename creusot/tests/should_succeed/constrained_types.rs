extern crate creusot_contracts;

use creusot_contracts::*;

extern_spec! {
    impl<U: PartialOrd<U> + Ord + Model, T: PartialOrd<T> + Ord + Model> PartialOrd for (U, T)
    where U::ModelTy: OrdLogic, T::ModelTy: OrdLogic
    {
        #[ensures(result == (@self).lt_log(@*o))]
        fn lt(&self, o: &(U, T)) -> bool;
    }
}

pub fn uses_concrete_instance(x: (u32, u32), y: (u32, u32)) -> bool {
    x < y
}
