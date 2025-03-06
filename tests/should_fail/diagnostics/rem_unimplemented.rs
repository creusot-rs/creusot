#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
fn remainder(x: i32, y: i32) -> i32 {
    // FIXME(diagnostics): Why is the error reported twice?
    x % y
}
