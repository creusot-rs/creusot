extern crate creusot_contracts;

use creusot_contracts::*;

pub fn f() {
    #[invariant(0 <= 1)]
    #[allow(while_true)]
    while true {}
}
