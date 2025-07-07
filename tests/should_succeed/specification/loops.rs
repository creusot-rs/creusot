extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(!x)]
pub fn while_loop_variant(x: bool) {
    #[variant(0)]
    while x {}
}
