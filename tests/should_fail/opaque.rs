extern crate creusot_contracts;

// INTENT: Should produce an error message because we reference `priv_symbol` which is
// less visible than we are opaque.

pub mod x {
    use creusot_contracts::*;

    #[logic]
    fn priv_symbol() -> bool {
        true
    }

    #[open(crate)]
    #[logic]
    pub fn bad() -> bool {
        priv_symbol()
    }
}
