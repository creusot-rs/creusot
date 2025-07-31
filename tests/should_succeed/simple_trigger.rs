// CREUSOT_ARG=--simple-triggers=true
extern crate creusot_contracts;

use creusot_contracts::*;

#[logic]
#[requires(i >= 0)]
#[variant(i)]
#[ensures(i == 0 ==> result == 0)]
pub fn id(i: Int) -> Int {
    if i == 0 { 0 } else { id(i - 1) + 1 }
}

#[ensures(id(1) == 1)]
pub fn test() {}
