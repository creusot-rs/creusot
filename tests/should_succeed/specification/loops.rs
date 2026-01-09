extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(!x)]
pub fn while_loop_variant(x: bool) {
    #[variant(0)]
    while x {}
}
