extern crate creusot_std;
use creusot_std::prelude::*;

unsafe fn evil() {}

#[ensures(true)]
pub fn main() {
    evil();
}
