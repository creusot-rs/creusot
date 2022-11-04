extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('x) -> 'x)]
fn test<'a: 'b, 'b, X>(x: &'a mut X) -> &'b mut X {
    x
}
