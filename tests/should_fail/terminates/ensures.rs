extern crate creusot_std;
use creusot_std::{mode::Mode, prelude::*};

#[ensures(|_, mode| !g(mode))]
pub fn f() {}

#[logic(prophetic)]
pub fn g(mode: Mode) -> bool {
    pearlite! {
        f.postcondition(mode, (), ())
    }
}
