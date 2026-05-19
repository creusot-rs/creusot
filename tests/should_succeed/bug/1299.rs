extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[requires(i@ >= 0)]
#[variant(i)]
pub fn count_paths(i: isize) {
    let _ = (0..i).map(|j| count_paths(j));
}

#[logic]
#[ensures(result == 0)]
#[variant(i)]
pub fn polyrec<T>(i: Int, x: T) -> Int {
    pearlite! {
        if i == 0 {
            0
        } else {
            polyrec(i - 1, ((), x))
        }
    }
}

#[ensures(polyrec(i, x) == 0)]
pub fn polyrec_<T>(i: Int, x: T) {
}

// #[check(terminates)]
// #[ensures(result@ == polyrec(i@, x))]
// #[variant(i)]
// pub fn ppolyrec<T>(i: usize, x: T) -> usize {
//     if i == 0 {
//         0
//     } else {
//         ppolyrec(i - 1, ())
//     }
// }
