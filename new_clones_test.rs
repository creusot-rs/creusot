extern crate creusot_contracts;
use creusot_contracts::{std::iter::*, *};

pub fn counter() {
    let mut a = 0;
    let x = (|| {
        a += 1;
        0 + 0
    })();
}
