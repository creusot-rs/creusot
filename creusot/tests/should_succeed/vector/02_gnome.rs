#![feature(type_ascription, unsized_fn_params)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

#[predicate]
fn sorted_range<T: Ord>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i : Int, j : Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted<T: Ord>(s: Seq<T>) -> bool {
    sorted_range(s, 0, s.len())
}

#[ensures(sorted(@^v))]
#[ensures((@^v).permutation_of(@*v))]
fn gnome_sort<T: Ord>(v: &mut Vec<T>) {
    let old_v = Ghost::record(&v);
    let mut i = 0;
    #[invariant(sorted, sorted_range(@v, 0, @i))]
    #[invariant(proph_const, ^v === ^@old_v)]
    #[invariant(permutation, (@*v).permutation_of(@*@old_v))]
    while i < v.len() {
        if i == 0 || v[i - 1].le(&v[i]) {
            i += 1;
        } else {
            v.swap(i - 1, i);
            i -= 1;
        }
    }
}
