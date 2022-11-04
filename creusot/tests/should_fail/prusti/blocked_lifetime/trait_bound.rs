extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(*x == 0u32)]
fn trait_bound<'a, X: Into<&'a u32>>(x: &'a mut u32){
    panic!()
}