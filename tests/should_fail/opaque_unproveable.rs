// WHY3PROVE
extern crate creusot_std;
use creusot_std::prelude::*;

mod x {
    use creusot_std::prelude::*;

    #[logic(open(self))]
    pub fn opaque() -> bool {
        true
    }
}

pub fn test() {
    // INTENT: Should not pass as the body of `x::opaque` is opaque (duh).
    proof_assert!(x::opaque());
}
