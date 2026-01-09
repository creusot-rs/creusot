extern crate creusot_std;

use creusot_std::prelude::*;

fn f() -> ! {
    loop {}
}

#[allow(unreachable_code)]
#[ensures(!b)]
pub fn g(b: bool) {
    if b {
        f();
    }
}
