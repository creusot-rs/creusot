extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

unsafe fn evil() {}

#[ensures(true)]
fn main() {
    evil();
}
