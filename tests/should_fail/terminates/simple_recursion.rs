#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[check(terminates)]
fn recurses(b: bool) {
    if b {
        recurses(!b);
    }
}
