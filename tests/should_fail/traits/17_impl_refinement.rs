// WHY3PROVE
extern crate creusot_std;
use creusot_std::prelude::*;

// Verifies that implementations can refine the contract of their encompassing trait

pub trait Tr {
    #[ensures(result@ >= 10)]
    fn my_function(&self) -> usize;
}

impl Tr for () {
    #[requires(true)]
    #[ensures(result@ >= 15)]
    fn my_function(&self) -> usize {
        20
    }
}

pub trait ReqFalse {
    #[logic]
    #[requires(x@ >= 10)]
    fn need_false(x: u64) -> ();
}

impl ReqFalse for () {
    // This should not prove
    #[logic]
    #[requires(y@ >= 15)]
    fn need_false(y: u64) {}
}
