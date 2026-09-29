extern crate creusot_std;
use creusot_std::prelude::*;

pub fn move_ghost_in_ghost() {
    ghost! {
        let a: Box<i32> = Box::new(1);
        ghost! {
            let b = a;
            assert!(*b == 1);
        };
    };
}

pub fn mut_ghost_in_ghost() {
    ghost! {
        let mut a: i32 = 1i32;
        assert!(a == 1);
        ghost! {
            a = 2;
        };
        assert!(a == 2);
    };
}
