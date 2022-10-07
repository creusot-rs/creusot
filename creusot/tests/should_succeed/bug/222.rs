// SHOULD_PROVE Z3 NO_SPLIT
extern crate creusot_contracts;
use creusot_contracts::{logic::Int, *};

trait A {
    #[logic]
    fn mktrue() -> Int {
        pearlite! { 5 }
    }

    #[law]
    #[ensures(Self::mktrue() <= 10)]
    fn is_true() {
        ()
    }
}

impl A for () {
    #[logic]
    fn mktrue() -> Int {
        pearlite! { 6 }
    }
}

// Should generate a VC for false
// impl A for bool {
//     #[logic]
//     fn mktrue() -> Int {
//         pearlite! { 15 }
//     }
// }
