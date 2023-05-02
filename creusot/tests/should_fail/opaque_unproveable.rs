extern crate creusot_contracts;
use creusot_contracts::*;

mod x {
    use creusot_contracts::*;

    #[open(self)]
    #[predicate]
    pub fn opaque() -> bool {
        true
    }
}

pub fn test() {
    // INTENT: Should not pass as the body of `x::opaque` is opaque (duh).
    proof_assert!(x::opaque());
}
