extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[ensures(*x == 0u32)]
fn clause2<'a, 'b>(x: &'a mut u32) -> &'b mut u32
where &'a u32: 'b{
    panic!()
}
