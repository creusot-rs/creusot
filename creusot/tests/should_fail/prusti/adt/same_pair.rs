extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub struct SamePair<X>(X, X);

#[open]
#[logic]
pub fn test_constructor<'a: 'b, 'b>(x: &'a mut u32, y: &'b mut u32) -> SamePair<&'a mut u32> {
    SamePair(x, y)
}