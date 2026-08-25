extern crate creusot_std;
use creusot_std::{invariant::GuardedBorrow, prelude::*};

#[ensures(^bor == 0i32)]
fn breaks_inv(bor: &mut i32) {
    *bor = 0;
}

#[ensures(guarded.guard()[^guarded.borrow])]
#[check(ghost)]
fn takes_guarded(guarded: GuardedBorrow<i32>) {}

#[ensures(result == 1i32)]
pub fn example() -> i32 {
    let mut x = 1i32;
    let bor = &mut x;

    let guarded = GuardedBorrow::new(bor, snapshot!(|x| x == 1i32));

    breaks_inv(guarded.borrow);

    *guarded.borrow = 1i32;

    takes_guarded(guarded);

    x
}

#[ensures(^bor == 0i32)]
fn breaks_inv_ghost(mut bor: Ghost<&mut i32>) {
    ghost! { **bor = 0 };
}

#[ensures(*result == 1i32)]
pub fn ghostified() -> Ghost<i32> {
    let mut x = ghost!(1i32);
    let bor = ghost!(&mut *x);

    let mut guarded = ghost!(GuardedBorrow::new(bor.into_inner(), snapshot!(|x| x == 1i32)));
    ghost_let!(mut borrow = &mut *guarded.borrow);

    breaks_inv_ghost(ghost!(&mut **borrow));

    // do some program step here...

    ghost! { **borrow = 1i32 }; // the guard _has_ to be restored through the reborrow

    ghost! { takes_guarded(guarded.into_inner()) };

    x
}
