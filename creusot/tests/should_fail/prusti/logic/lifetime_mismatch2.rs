extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('x) -> 'x)]
fn test<'a: 'b, 'b: 'a, 'c, X>(x: &'c mut &'a mut X) -> &'c mut &'b mut X {
    x
}
