extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[logic(('x, 'y) -> 'y)]
fn test<X, Y>(x: X, _: Y) -> X {
    x
}
