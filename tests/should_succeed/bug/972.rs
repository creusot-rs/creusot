#![feature(never_type)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
#[open]
pub fn absurd(x: !) -> bool {
    match x {}
}

#[requires(match x {})]
#[requires(absurd(match x {}))] // test case where empty match is not wrapped in a cast
#[allow(unreachable_code)]
pub fn foo(x: !) {
    match x {}
}

#[ensures(match x {Some(x) => x, None => true})]
pub fn bar(x: Option<!>) {
    match x {
        Some(x) => x,
        None => (),
    }
}
