extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(*x == 0u32)]
fn clause1<'a, 'b>(x: &'a mut u32) -> &'b mut u32
    where 'a: 'b{
    panic!()
}
