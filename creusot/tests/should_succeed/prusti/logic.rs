#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic]
pub fn simple<X>(x: X) -> X {
    x
}

#[allow(unconditional_recursion)]
#[open]
#[logic]
pub fn unreachable<'a, X>() -> &'a mut X {
    unreachable::<X>()
}

#[open]
#[logic]
#[ensures(result == *x)]
pub fn cur<'a, X: SnapEq>(x: &'a mut X) -> X {
    *x
}

#[open]
#[logic('x)]
#[ensures(result == *x)]
pub fn fin<'now, X: SnapEq>(x: &'now mut X) -> X {
    *x
}

#[open]
#[logic]
#[after_expiry('now, *result == *x)]
pub fn expiry<'a, X: SnapEq>(x: &'a mut X) -> &'a mut X {
    x
}

#[open]
#[logic('_)]
pub fn check_plain(x: u32) -> u32 {
    x
}

#[open]
#[logic('_)]
pub fn check_plain_tuple(x: (bool, f32)) -> (bool, f32) {
    x
}
