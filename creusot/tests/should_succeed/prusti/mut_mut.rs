extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic('_, '_)]
#[ensures(result)]
pub fn v1<'a, 'b, 'c, X>(x: &'c mut &'a mut X, y: &'c mut &'b mut X) -> bool {
    true
}

#[open]
#[logic('x, 'y)]
#[ensures(result)]
pub fn v2<'x, 'y, 'a, 'c, X>(x: &'c mut &'a mut X, y: &'c mut &'a mut X) -> bool {
    v1(at_expiry::<'x>(x), at_expiry::<'y>(y))
}