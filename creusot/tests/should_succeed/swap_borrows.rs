extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result === (x.1, x.0))]
fn swap<T>(x: (T, T)) -> (T, T) {
    (x.1, x.0)
}

//  The required permission Acc(_5.tuple_1.val_ref, read) cannot be obtained.
fn main() {
    let (mut a, mut b) = (0, 0);
    let p = swap((&mut a, &mut b));
    *p.0 = 10;

    proof_assert! { b == 10u32 };
    proof_assert! { a == 0u32 };
}
