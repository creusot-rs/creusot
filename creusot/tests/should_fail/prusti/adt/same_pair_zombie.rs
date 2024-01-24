extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub struct SamePair<X>(X, X);

#[open]
#[logic('x, 'curr where 'curr: 'x)]
pub fn test_constructor<'x>(x: Box<u32>, y: Box<u32>) -> SamePair<Box<u32>> {
    SamePair(at::<'x>(x), y)
}
