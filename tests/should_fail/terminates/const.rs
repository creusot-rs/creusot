extern crate creusot_std;
use creusot_std::prelude::*;

pub struct False;

impl Invariant for False {
    #[logic]
    fn invariant(self) -> bool {
        false
    }
}

pub const C: False = {
    proof_assert! { let _ = f(); false };
    False
};

#[logic]
#[ensures(false)]
pub fn f() {
    proof_assert!( let _ = C; false );
}
