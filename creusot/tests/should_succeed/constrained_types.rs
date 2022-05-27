// WHY3SKIP

extern crate creusot_contracts;

use creusot_contracts::*;


extern_spec! {
    impl<K: PartialOrd<K> + Ord + Model, L: PartialOrd<L> + Ord + Model> PartialOrd for (K, L)
    where K::ModelTy: OrdLogic, L::ModelTy: OrdLogic
    {
        #[ensures(result == (@self).lt_log(@*o))]
        fn lt(&self, o: &(K, L)) -> bool;
    }
}

pub fn uses_concrete_instance(x: (u32, u32), y: (u32, u32)) -> bool {
    x < y
}
