extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(true)]
fn simple<'curr>(x: &'curr mut u32) -> &'curr mut u32 {
    panic!()
}
