extern crate creusot_contracts;
use creusot_contracts::{std::ops::*, *};

pub fn multi_use<T>(x: &T) {
    let c =
    || {
        let _ = x;
    };
}

