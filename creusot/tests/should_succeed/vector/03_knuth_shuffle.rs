// WHY3PROVE CVC4
#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

#[trusted]
#[requires(@l <= @u)]
#[ensures(@l <= @result && @result  < @u)]
fn rand_in_range(l: usize, u: usize) -> usize {
    use creusot_contracts::rand::Rng;
    rand::thread_rng().gen_range(l..u)
}

#[ensures((@^v).permutation_of(@v))]
fn knuth_shuffle<T>(v: &mut Vec<T>) {
    let old_v = Ghost::record(&v);
    let mut n = 0;

    #[invariant(permutation, (@v).permutation_of(@@old_v))]
    #[invariant(proph_const, ^v === ^@old_v)]
    while n < v.len() {
        // We assign the length to a variable to work around a limitation with two-phase borrows
        // where we forget the value stored in the reference.
        let i = rand_in_range(0, v.len() - n);
        v.swap(i, v.len() - n - 1);
        n += 1;
    }
}
