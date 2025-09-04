extern crate creusot_contracts;
use creusot_contracts::*;

unsafe fn evil() {}

#[ensures(true)]
pub fn main() {
    evil();
}
