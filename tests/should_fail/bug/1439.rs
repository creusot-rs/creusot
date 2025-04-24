// SHORT_ERROR
extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(match opt { })]
fn foo(opt: Option<i32>) {}
