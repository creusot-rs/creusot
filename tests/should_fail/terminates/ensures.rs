extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(!g())]
pub fn f() {}

#[logic(prophetic)]
pub fn g() -> bool {
    pearlite! {
        f.postcondition((), ())
    }
}
