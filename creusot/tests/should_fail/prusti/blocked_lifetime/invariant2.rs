extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;
use std::cell::Cell;

#[ensures(*x == 0u32)]
fn invariant2<'a>(x: &'a mut u32, _: Cell<&'a u32>){
    panic!()
}