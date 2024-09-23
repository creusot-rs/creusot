extern crate creusot_contracts;

use creusot_contracts::{invariant::Invariant, *};

pub struct IsZero(i32);

impl Invariant for IsZero {
    #[predicate(prophetic)]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! { self.0 == 0i32 }
    }
}

pub fn test_open_inv_param(#[creusot::open_inv] _: IsZero) {}
pub fn test_open_inv_param_call() {
    let mut a = IsZero(0);
    a.0 -= 1;
    test_open_inv_param(a);
}

#[open_inv_result]
pub fn test_open_inv_result() -> IsZero {
    let mut a = IsZero(0);
    a.0 -= 1;
    a
}
