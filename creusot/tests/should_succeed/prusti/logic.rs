extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic(('x) -> 'x)]
pub fn simple<X>(x: X) -> X {
    x
}


#[allow(unconditional_recursion)]
#[open]
#[logic(() -> 'x)]
pub fn unreachable<'a, X>() -> &'a mut X {
    unreachable::<X>()
}

#[open]
#[logic(('curr) -> 'curr)]
#[ensures(result == *x)]
pub fn cur<'a, X>(x: &'a mut X) -> X {
    *x
}

#[open]
#[logic(('x) -> 'curr)]
#[ensures(result == *x)]
pub fn fin<'curr, X>(x: &'curr mut X) -> X {
    *x
}

#[open]
#[logic(('x) -> 'x)]
#[after_expiry('x, *result == *x)]
#[after_expiry('a, *result == *x)]
pub fn expiry<'a, X>(x: &'a mut X) -> &'a mut X {
    x
}
