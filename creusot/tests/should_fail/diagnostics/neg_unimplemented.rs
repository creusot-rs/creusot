#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
fn negation(x: i32) -> i32 {
    // FIXME(diagnostics): Why is the error reported twice?
    -x
}
