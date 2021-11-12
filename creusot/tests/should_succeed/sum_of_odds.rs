// Toy example testing the lemma function feature of Creusot

extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
fn sqr(x: Int) -> Int {
    x * x
}

#[predicate]
fn is_square(y: Int) -> bool {
    pearlite! { exists<z: Int> y === sqr(z) }
}

#[logic]
#[variant(x)]
fn sum_of_odd(x: Int) -> Int {
    if x <= 0 {
        0
    } else {
        sum_of_odd(x - 1) + 2 * x - 1
    }
}

#[logic]
#[requires(x >= 0)]
#[ensures(sum_of_odd(x) === sqr(x))]
#[variant(x)]
fn sum_of_odd_is_sqr(x: Int) {
    pearlite! { if x > 0 { sum_of_odd_is_sqr(x-1) } else { () } }
}

#[requires(@x < 0x10000)]
#[ensures(@result === sum_of_odd(@x))]
fn compute_sum_of_odd(x: u32) -> u32 {
    let mut s: u32 = 0;
    let mut i: u32 = 0;
    #[invariant(i_bound, @i <= @x)]
    #[invariant(s_is_sum, @s === sum_of_odd(@i))]
    while i < x {
        proof_assert! { {
        sum_of_odd_is_sqr(@i);
        true }}
        s += 2 * i + 1;
        i += 1;
    }
    return s;
}

#[requires(@x < 0x10000)]
fn test(x: u32) {
    let y = compute_sum_of_odd(x);
    proof_assert! { {
        sum_of_odd_is_sqr(@x);
        is_square(@y)
    } }
}
