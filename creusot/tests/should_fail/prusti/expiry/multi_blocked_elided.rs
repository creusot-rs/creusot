extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[after_expiry(true)]
fn test<'a>(x: &mut &mut u32, y: &mut &mut u32){

}