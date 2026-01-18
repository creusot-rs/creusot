extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn triangular(n: Int) -> Int {
    pearlite! { n * (n + 1) / 2 }
}

#[requires(triangular(n@) <= u32::MAX@)]
#[ensures(result@ == triangular(n@))]
pub fn sum_first_n_iter(n: usize) -> usize {
    let mut sum = 0;
    let () = (1..=n)
        .map_inv(|x, produced| {
            proof_assert! { x@ == produced.len() + 1 };
            sum += x;
            proof_assert! { sum@ == triangular(x@) };
        })
        .collect();
    sum
}
