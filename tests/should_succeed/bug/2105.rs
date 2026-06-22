extern crate creusot_std;
use creusot_std::prelude::*;

// FIXME remove this requires and use print! instead of panic!
#[requires(false)]
pub fn a() {
    panic!("a {}", true);
}
