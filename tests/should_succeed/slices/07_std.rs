extern crate creusot_std;
use creusot_std::prelude::*;

pub fn fill() {
    let mut test = creusot_std::vec!(0; 10);
    test.fill(42);
    let x = test[3];
    proof_assert!(x == 42usize);
}

pub fn fill_with() {
    let mut test = creusot_std::vec!(0; 10);
    let mut i = 0;
    test.fill_with(|| {
        let res = i;
        i += 1;
        res
    });
    let x = test[5];
    proof_assert!(x == 5usize);
}
