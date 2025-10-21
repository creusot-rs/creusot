extern crate creusot_contracts;
use creusot_contracts::{invariant::*, prelude::*};

pub struct Zero<T>(u32, T);

impl<T> Invariant for Zero<T> {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! { self.0@ == 0 }
    }
}

pub fn f<T>(x: Zero<T>, y: Zero<T>) {
    let clos = #[ensures(result@ == 0)]
    || {
        proof_assert!(x.0@ == 0);
        let clos2 = #[ensures(result@ == 0)]
        || {
            proof_assert!(y.0@ == 0);
            (*&y).0
        };
        clos2();
        (*&x).0
    };
    clos();
}
