#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
fn division(x: i32, y: i32) -> i32 {
    // FIXME(diagnostics): Why is the error reported twice?
    x / y
}
