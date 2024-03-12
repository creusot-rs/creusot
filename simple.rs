extern crate creusot_contracts;
use creusot_contracts::*;

// #[ensures(result >= 0u32)]
// fn test(x : bool) -> u32 {
//   if x {
//     // assert!(false);
//     0
//   } else {
//     1
//   }
// }

// #[requires(0 < 0)]
// #[ensures(1 < 1)]
// fn callee<T>(a: T) {}

// fn call<T>(x: T) {
//   callee(x);
//   proof_assert!(2 < 2);
// }

// fn loop_() {
//     while true {
//         callee(0);
//     }
// }

// fn sum(a: u32, b: u32) -> u32 {
//     a + b
// }

// fn borrow(x : &mut u32) {
//     * x = 0;
// }

#[requires(n@ < 1000)]
#[ensures(result@ == n@ * (n@ + 1) / 2)]
pub fn sum_first_n(n: u32) -> u32 {
    let mut sum = 0;
    #[invariant(sum@ == produced.len() * (produced.len() + 1) / 2)]
    for i in 1..=n {
        sum += i;
    }
    sum
}
