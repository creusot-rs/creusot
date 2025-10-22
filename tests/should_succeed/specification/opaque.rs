extern crate creusot_contracts;
use creusot_contracts::prelude::*;

mod x {
    use creusot_contracts::prelude::*;

    #[logic(open)]
    pub fn transparent() -> bool {
        true
    }

    #[logic(open(crate))]
    pub fn transparent_crate() -> bool {
        true
    }
}

pub fn test() {
    proof_assert!(x::transparent());
    proof_assert!(x::transparent_crate());
}
