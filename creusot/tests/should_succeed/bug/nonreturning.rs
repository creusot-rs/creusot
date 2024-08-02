extern crate creusot_contracts;

use creusot_contracts::*;

fn f() -> ! {
    loop { }
}

#[allow(unreachable_code)]
#[ensures(!b)]
pub fn g(b: bool) {
    if b {
        f();
    }
}