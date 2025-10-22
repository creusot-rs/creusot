extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub fn ghost_only() {
    ghost! {
        let x = 1i32;
        proof_assert!(x == 1i32);
    };
}

pub fn ghost_capture() {
    let x = 42i32;

    ghost! {
        let y = x;
        proof_assert!(y == 42i32);
    };
}

pub fn ghost_mutate() {
    let mut p = ghost! {(2i32, 3i32)};

    ghost! {
        p.0 = 4;
    };

    ghost! {
        proof_assert!(p.0 == 4i32);
        proof_assert!(p.1 == 3i32);
    };
}
