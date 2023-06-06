//! An adaptation of
//!
//! https://rosettacode.org/wiki/100_doors#Rust
//!
//! See also the similar example in Prusti:
//!
//! https://github.com/viperproject/prusti-dev/blob/b9c5b83d930ef0f648347a930658b4986a0ae774/prusti-tests/tests/verify_overflow/pass/rosetta/100_doors.rs
//!
//! Verified properties:
//!
//! +   Absence of panics
//! +   Absence of integer overflows
//! +   Absence of array access out of bounds

extern crate creusot_contracts;
use creusot_contracts::{vec, *};

pub fn f() {
    let mut door_open: Vec<bool> = vec![false; 100];
    #[invariant(door_open@.len() == 100)]
    for pass in 1..101 {
        let mut door: usize = pass;
        #[invariant(1 <= door@ && door@ <= 100 + pass@)]
        #[invariant(door_open@.len() == 100)]
        while door <= 100 {
            door_open[door - 1] = !door_open[door - 1];
            door += pass;
        }
    }
}
