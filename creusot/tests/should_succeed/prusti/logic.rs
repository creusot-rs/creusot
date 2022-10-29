extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[logic(('x) -> 'x)]
pub fn simple<X>(x: X) -> X {
    x
}


#[allow(unconditional_recursion)]
#[logic(() -> 'x)]
pub fn unreachable<'a, X>() -> &'a mut X {
    unreachable::<X>()
}

#[logic(('curr) -> 'curr)]
#[ensures(result == *x)]
pub fn cur<'a, X>(x: &'a mut X) -> X {
    *x
}

#[logic(('x) -> 'curr)]
#[ensures(result == *x)]
pub fn fin<'curr, X>(x: &'curr mut X) -> X {
    *x
}

#[logic(('x) -> 'x)]
#[after_expiry('x, *result == *x)]
#[after_expiry('a, *result == *x)]
pub fn expiry<'a, X>(x: &'a mut X) -> &'a mut X {
    x
}
