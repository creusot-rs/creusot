#![allow(unreachable_patterns)]
#![feature(exclusive_range_pattern)]

extern crate creusot_contracts;

// Test that matching constant integer values works
pub fn f() {
    match 1 {
        0..10 => {
            assert!(true)
        }
        5 | 6 => {
            assert!(false)
        }
        _ => {
            assert!(false)
        }
    }
}
