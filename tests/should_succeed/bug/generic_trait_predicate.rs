extern crate creusot_contracts;

use creusot_contracts::*;

pub trait CP {
    #[open]
    #[predicate]
    fn match_t<K>() -> bool {
        pearlite! { Self::match_n::<K>() }
    }

    #[predicate]
    fn match_n<K>() -> bool;
}

impl<L, R> CP for (L, R) {
    #[open]
    #[predicate]
    fn match_n<N>() -> bool {
        pearlite! { true }
    }
}
