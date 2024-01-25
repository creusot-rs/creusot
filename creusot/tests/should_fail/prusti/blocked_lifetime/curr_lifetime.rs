extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(true)]
fn simple<'post>(x: &'post mut u32) -> &'post mut u32 {
    panic!()
}
