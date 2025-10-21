extern crate creusot_contracts;
use creusot_contracts::prelude::*;

unsafe fn evil() {}

#[ensures(true)]
pub fn main() {
    evil();
}
