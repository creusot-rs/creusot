extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
#[open]
pub fn my_eq1<X: SnapEq>(x: X, y: X) -> bool {
    x == y
}
#[logic]
#[open]
pub fn my_eq2<X>(x: X, y: X) -> bool {
    my_eq1(x, y)
}
