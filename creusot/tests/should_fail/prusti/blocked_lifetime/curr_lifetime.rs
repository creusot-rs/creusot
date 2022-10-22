extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[ensures(true)]
fn simple<'curr>(x: &'curr mut u32) -> &'curr mut u32 {
    panic!()
}
