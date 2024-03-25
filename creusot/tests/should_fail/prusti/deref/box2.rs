extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(result == x.0)]
pub fn project_deref_bad<'a>(x: Box<(u32, u32)>) -> u32 {
    (*x).0
}
