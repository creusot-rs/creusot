extern crate creusot_contracts;
use creusot_contracts::prelude::*;

// Prove that this function implements the sum of the first n natural numbers.
// Hint: there exists a closed form of this sum
pub fn sum_first_n(n: u32) -> u32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {
        i += 1;
        sum += i;
    }
    sum
}
