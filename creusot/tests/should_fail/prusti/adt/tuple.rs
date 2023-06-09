extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic(('x, 'x) -> 'x)]
pub fn test_constructor<'a, 'b, 'c>(x: &'a mut u32, y: &'b mut u32) -> (&'c mut u32, &'c mut u32) {
    (x, y)
}