extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('_, '_) -> 'x)]
#[ensures(result)]
pub fn v1<'a, 'b, 'c, X>(x: &'c mut &'a mut X, y: &'c mut &'b mut X) -> bool {
    true
}

#[logic(('_, '_) -> 'x)]
#[ensures(result)]
pub fn v2<'a, 'c, X>(x: &'c mut &'a mut X, y: &'c mut &'a mut X) -> bool {
    v1(x, y)
}