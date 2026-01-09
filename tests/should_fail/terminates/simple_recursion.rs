#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
fn recurses(b: bool) {
    if b {
        recurses(!b);
    }
}
