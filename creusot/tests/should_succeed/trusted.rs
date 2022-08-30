extern crate creusot_contracts;

use creusot_contracts::*;

#[trusted]
pub fn call_external() {
    println!("Hello world!");
}

#[trusted]
#[ensures(result == 10u32)]
pub fn lie() -> u32 {
    5 // I'm evil
}

#[ensures(result == 10u32)]
pub fn victim_of_lie() -> u32 {
    lie()
}

#[predicate]
#[trusted]
pub fn trusted_pred(_x: u32) -> bool {
    true
}
