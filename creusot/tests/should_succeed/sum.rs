extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(n@ < 1000)]
#[ensures(result@ == n@ * (n@ + 1) / 2)]
pub fn sum_first_n(n: u32) -> u32 {
    let mut sum = 0;
    #[invariant(sum_value, sum@ == produced.len() * (produced.len() - 1) / 2)]
    for i in 0..=n {
        sum += i;
    }
    sum
}
