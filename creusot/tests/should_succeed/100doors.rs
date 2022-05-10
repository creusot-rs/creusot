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
use creusot_contracts::*;

fn main() {
    let mut door_open: Vec<bool> = Vec::with_capacity(100);
    let mut i: usize = 1;
    #[invariant(loop_bounds,1 <= @i && @i <= 101)]
    #[invariant(door_size, (@door_open).len() == @i - 1)]
    while i < 101 {
        door_open.push(false);
        i += 1;
    }
    // alternative 1: not supported
    //let mut door_open: Vec<bool> = vec![false;100];
    // alternative 2: not supported
    //let mut door_open: Vec<bool> = Vec::new();
    //door_open.resize(100,false);
    assert!(door_open.len() == 100);
    let mut pass: usize = 1;
    #[invariant(loop_bounds,1 <= @pass && @pass <= 101)]
    #[invariant(door_size, (@door_open).len() == 100)]
    while pass < 101 {
        let mut door: usize = pass;
        #[invariant(loop_bounds,1 <= @door && @door <= 100 + @pass)]
        #[invariant(door_size, (@door_open).len() == 100)]
        while door <= 100 {
            door_open[door - 1] = !door_open[door - 1];
            door += pass;
        }
        pass += 1;
    }
}
