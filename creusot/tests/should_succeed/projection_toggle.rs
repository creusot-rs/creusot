#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(equal(toggle, true) ==> (equal(result, a) && equal(^b, *b)))]
#[ensures(equal(toggle, false) ==> (equal(result, b) && equal(^a, *a)))]
fn proj_toggle<'a, T: PartialEq>(toggle: bool, a: &'a mut T, b: &'a mut T) -> &'a mut T {
    if toggle {
        a
    } else {
        b
    }
}

fn main() {
    let mut a = 10;
    let mut b = 5;

    let x = proj_toggle(true, &mut a, &mut b);

    *x += 5;
    assert!(a == 15);
}
