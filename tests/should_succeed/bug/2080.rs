extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;

#[trusted]
mod m {
    unsafe impl Send for super::S {}
}
