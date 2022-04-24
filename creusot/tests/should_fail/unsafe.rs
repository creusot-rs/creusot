extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

unsafe fn evil() {}

#[ensures(true)]
fn main() {
    evil();
}
