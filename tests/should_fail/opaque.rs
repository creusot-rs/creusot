extern crate creusot_std;

// INTENT: Should produce an error message because we reference `priv_symbol` which is
// less visible than we are opaque.

pub mod x {
    use creusot_std::prelude::*;

    #[logic]
    fn priv_symbol() -> bool {
        true
    }

    #[logic(open(crate))]
    pub fn bad() -> bool {
        priv_symbol()
    }
}
