extern crate creusot_contracts;
use creusot_contracts::*;

#[variant(x)]
pub fn variant_is_not_checked(x: u32) {
    if x != 0 {
        variant_is_not_checked(x); // Whoops
    }
}
