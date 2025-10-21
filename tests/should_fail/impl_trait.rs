// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub trait MyTrait {
    fn a(&self) -> bool;
}

impl MyTrait for () {
    #[ensures(result)]
    fn a(&self) -> bool {
        true
    }
}

pub fn returns_iterator() -> impl MyTrait {
    ()
}

#[ensures(true)]
pub fn main() {
    let x = returns_iterator().a();

    proof_assert!(x);
}
