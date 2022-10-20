extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[ensures(*x == 0u32)]
fn implied<'a, 'b>(x: &'a mut u32, _: &'b &'a u32) -> &'b mut u32 {
    panic!()
}
