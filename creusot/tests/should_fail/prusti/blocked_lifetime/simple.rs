extern crate creusot_contracts;
use creusot_contracts::prusti::*;


#[ensures(*x == 0u32)]
fn simple(x: &mut u32) -> &mut u32 {
    panic!()
}