extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
fn any<T: Default>() -> T {
    Default::default()
}

/// Test integer patterns in programs (there was a bug where negative values came out positive)
pub fn f() {
    let x = any::<i8>();
    let y = match x {
        -1i8 => -1i8,
        -128 => -128,
        127 => 127,
        _ => x,
    };
    proof_assert! { x == y };
    let x = any::<i16>();
    let y = match x {
        -1i16 => -1i16,
        -32768 => -32768,
        32767 => 32767,
        _ => x,
    };
    proof_assert! { x == y };
    let x = any::<i32>();
    let y = match x {
        -1i32 => -1i32,
        -2147483648 => -2147483648,
        2147483647 => 2147483647,
        _ => x,
    };
    proof_assert! { x == y };
    let x = any::<i64>();
    let y = match x {
        -1i64 => -1i64,
        -9223372036854775808 => -9223372036854775808,
        9223372036854775807 => 9223372036854775807,
        _ => x,
    };
    proof_assert! { x == y };
    let x = any::<i128>();
    let y = match x {
        -1i128 => -1i128,
        -170141183460469231731687303715884105728 => -170141183460469231731687303715884105728,
        170141183460469231731687303715884105727 => 170141183460469231731687303715884105727,
        _ => x,
    };
    proof_assert! { x == y };
    let x = any::<u32>();
    let y = match x {
        4294967295u32 => 4294967295u32,
        _ => x,
    };
    proof_assert! { x == y };
    let x = any::<u128>();
    let y = match x {
        340282366920938463463374607431768211455u128 => 340282366920938463463374607431768211455u128,
        _ => x,
    };
    proof_assert! { x == y };
}
