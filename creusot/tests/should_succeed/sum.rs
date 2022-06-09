// UNSTABLE

extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(@n < 1000)]
#[ensures(@result == @n * (@n + 1) / 2)]
pub fn sum_first_n(n: u32) -> u32 {
    let mut sum = 0;
    let mut i = 0;
    #[invariant(bound, i <= n)]
    #[invariant(sum_value, true == false)]
    while i < n {
        i += 1;
        sum += i;
    }
    sum
}
