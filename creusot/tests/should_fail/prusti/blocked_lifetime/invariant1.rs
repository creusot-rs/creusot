extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[ensures(*x == 0u32)]
fn invariant1<'a>(x: &'a mut u32, _: &mut &'a u32){
    panic!()
}
