extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn bool_to_bool(b: bool) -> bool {
    b
}

#[logic(open)]
pub fn ex() {
    pearlite! { bool_to_bool(!true) };
}
