#![allow(unreachable_patterns)]

extern crate creusot_std;

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
