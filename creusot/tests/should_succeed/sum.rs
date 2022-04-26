extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(@n < 1000)]
#[ensures(result == n * (n + 1u32) / 2u32)]
fn sum_first_n(n: u32) -> u32 {
    let mut sum = 0;
    let mut i = 0;
    #[invariant(bound, i <= n)]
    #[invariant(sum_value, sum == i * (i + 1u32) / 2u32)]
    while i < n {
        i += 1;
        sum += i;
    }
    sum
}

fn main() {}
