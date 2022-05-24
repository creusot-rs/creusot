extern crate creusot_contracts;

use creusot_contracts::*;

// #[requires(0 < @n && @n < 10000)]
// fn knapsack01_dyn<Name>(n: usize) {
//     let i: usize = 0;

//     let mut w = 1;

//     #[invariant(i_items_len, @i < @n)]
//     while w <= n {
//         w += 1
//     }

//     let i = n;
// }

fn test_233() {
    let x = 17;
    proof_assert!( @x == 17 );
    let x = 42;
    proof_assert!( @x == 42 );
}
