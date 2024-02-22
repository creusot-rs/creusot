extern crate creusot_contracts;
use creusot_contracts::*;

// Since we reborrow `bor` after `b1`, its prophecy depends on `b2` and not `b1`
pub fn not_final_borrow<T>(bor: &mut T) {
    let b1 = &mut *bor;
    proof_assert!(b1 == bor);
    let _b2 = &mut *bor;
}

pub fn store_changes_prophecy<T>(bor: &mut T, x: T) {
    let b1 = &mut *bor;
    // The prophecy of `bor` changed here after the reborrow
    *bor = x;
    proof_assert!(b1 == bor);
}

pub fn call_changes_prophecy(bor: &mut i32) {
    fn inner() -> i32 {
        2
    }
    let b1 = &mut *bor;
    // The prophecy of `bor` changed here after the reborrow
    *bor = inner();
    proof_assert!(b1 == bor);
}

// When unnesting, we can't statically track the prophecy in the inner borrow
#[ensures(result == &mut (**x).0)]
pub fn unnesting_fails<'a: 'b, 'b, T>(x: &'a mut &'b mut (T, T)) -> &'b mut T {
    &mut (**x).0
}

// Right now, we don't reason about the indices when tracking reborrows
#[requires(x@.len() >= 1)]
#[ensures(result == x.to_mut_seq()[0])]
pub fn indexing<T>(x: &mut [T]) -> &mut T {
    &mut x[0]
}
