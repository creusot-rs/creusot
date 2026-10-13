#![allow(unused)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
fn foo_log() -> i64 {
    foo()
}

#[logic_alias(foo_log)]
fn foo() -> i64 {
    0
}
