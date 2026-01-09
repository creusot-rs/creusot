extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(if toggle { result == a && ^b == *b } else { result == b && ^a == *a })]
fn proj_toggle<'a, T: PartialEq>(toggle: bool, a: &'a mut T, b: &'a mut T) -> &'a mut T {
    if toggle { a } else { b }
}

pub fn f() {
    let mut a = 10;
    let mut b = 5;

    let x = proj_toggle(true, &mut a, &mut b);

    *x += 5;
    assert!(a == 15);
}
