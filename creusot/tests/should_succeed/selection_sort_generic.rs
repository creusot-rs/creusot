#![feature(type_ascription)]
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

#[predicate]
fn sorted_range<T: Ord>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i: Int, j :Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted<T: Ord>(s: Seq<T>) -> bool {
    pearlite! {
        sorted_range(s, 0, s.len())
    }
}

#[predicate]
fn smaller_than<T: Ord>(s: Seq<T>, e: T, l: Int) -> bool {
    pearlite! {
        forall<j: Int> l < j && j < s.len() ==>
            e <= s[j]
    }
}

#[predicate]
fn larger_than<T: Ord>(s: Seq<T>, e: T, u: Int) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < u && i < s.len() ==>
            e >= s[i]
    }
}

#[predicate]
fn all_smaller<T: Ord>(s: Seq<T>, u: Int) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < u && i < s.len() ==>
            smaller_than(s, s[i], u)
    }
}

#[predicate]
fn all_larger<T: Ord>(s: Seq<T>, l: Int) -> bool {
    pearlite! {
        forall<i: Int> l <= i && i < s.len() ==>
            larger_than(s, s[i], l)
    }
}

#[predicate]
fn selection_sort_invariant<T: Ord>(s: Seq<T>, i: Int) -> bool {
    all_larger(s, i) && all_smaller(s, i)
}

#[predicate]
fn min_larger<T: Ord>(s: Seq<T>, u: Int, idx: Int) -> bool {
    pearlite! { forall<j: Int> 0 <= j && j < u ==> s[j] <= s[idx] }
}

#[predicate]
fn min_smaller<T: Ord>(v: Seq<T>, i: Int, min: Int) -> bool {
    pearlite! { forall<j: Int> i <= j && j < v.len() ==> v[min] <= v[j] }
}

#[ensures(sorted(@^v))]
#[ensures((@^v).permutation_of(@v))]
fn selection_sort<T: Ord>(v: &mut Vec<T>) {
    let mut i: usize = 0;
    let old_v = Ghost::record(&v);
    #[invariant(proph_const, ^v === ^@old_v)]
    #[invariant(permutation, (@v).permutation_of(@*@old_v))]
    #[invariant(i_bound, 0 <= @i && @i <= (@v).len())]
    #[invariant(sorted, sorted_range(@v, 0, @i))]
    #[invariant(sort_inv, selection_sort_invariant(@v, @i))]
    while i < v.len() {
        let mut min = i;
        let mut j = i + 1;
        #[invariant(min_is_min, forall<k: Int> @i <= k && k < @j ==> (@v)[@min] <= (@v)[k])]
        #[invariant(j_bound, @i <= @j && @j <= (@v).len())]
        #[invariant(min_bound, @i <= @min && @min < (@v).len() && @min <= @j)]
        while j < v.len() {
            if v[j].lt(&v[min]) {
                min = j;
            }
            j += 1;
        }
        proof_assert! { min_larger(@v, @i, @min) }
        proof_assert! { min_smaller(@v, @i, @min) }
        v.swap(i, min);
        i += 1;
        proof_assert! { sorted_range(@v, 0, @i) }
        proof_assert! { selection_sort_invariant(@v, @i) }
    }
}
