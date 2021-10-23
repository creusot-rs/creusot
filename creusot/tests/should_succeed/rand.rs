extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result >= 0u32)]
fn try_rand() -> u32 {
    if rand::random() {
        7u32
    } else {
        rand::random()
    }
}
