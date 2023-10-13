extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[after_expiry('a, *old(x) == 0u32)]
pub fn project_deref_bad<'a>(x: &u32, y: &'a u32) -> &'a u32 {
    y
}