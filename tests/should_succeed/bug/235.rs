extern crate creusot_std;

use creusot_std::prelude::*;

pub fn f() {
    #[invariant(0 <= 1)]
    #[allow(while_true)]
    while true {}
}
