extern crate creusot_contracts;

use creusot_contracts::*;

// TODO: these could be unit tests in the why3 crate

#[ensures(5 == 3 ==> 2 + 1 == 3)]
#[ensures(5 * 3 / 2 != 4 * (40 + 1))]
#[ensures(x.0 == x.1)]
fn respect_prec(x: (u32, u32)) {}

#[ensures(@0u32 + @1u32 == 0)]
fn respect_assoc() {}
