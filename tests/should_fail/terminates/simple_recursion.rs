#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[check(terminates)]
fn recurses(b: bool) {
    if b {
        recurses(!b);
    }
}
