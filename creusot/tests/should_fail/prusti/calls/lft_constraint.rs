extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(strange_constraint(result))]
fn test<'a, 'b>(x: &'a u32, y: &'b u32) -> (&'a u32, &'b u32) {
    (x, y)
}

#[logic('now where 'a: 'b)]
fn strange_constraint<'a, 'b>(t: (&'a u32, &'b u32)) -> bool {
    true
}
