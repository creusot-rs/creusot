#![allow(unused)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic_alias(^x)]
fn identity_prophetic(x: &mut usize) -> usize {
    *x = 10;
    *x
}
