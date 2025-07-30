extern crate creusot_contracts;
use creusot_contracts::*;

mod x {
    use creusot_contracts::*;

    #[open]
    #[logic]
    pub fn transparent() -> bool {
        true
    }

    #[open(crate)]
    #[logic]
    pub fn transparent_crate() -> bool {
        true
    }
}

pub fn test() {
    proof_assert!(x::transparent());
    proof_assert!(x::transparent_crate());
}
