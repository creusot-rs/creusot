#![feature(type_ascription)]
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

pub struct Ghost<T>(*mut T)
where
    T: ?Sized;

impl<T> Model for Ghost<T> {
    type ModelTy = T;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> Ghost<T> {
    #[trusted]
    #[ensures(@result === *a)]
    fn record(a: &T) -> Ghost<T> {
        panic!()
    }
}

#[predicate]
fn sorted_range(s: Seq<i32>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i: Int, j : Int> l <= i && i < j && j < u ==> s[i] <= (s[j])
    }
}

#[predicate]
fn sorted(s: Seq<i32>) -> bool {
    pearlite! {
        sorted_range(s, 0, s.len())
    }
}

#[predicate]
fn smaller_than(s: Seq<i32>, e: i32, l: Int) -> bool {
    pearlite! {
        forall<j: Int> l < j && j < s.len() ==>
            e <= s[j]
    }
}

#[predicate]
fn larger_than(s: Seq<i32>, e: i32, u: Int) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < u && i < s.len() ==>
            e >= s[i]
    }
}

#[predicate]
fn all_smaller(s: Seq<i32>, u: Int) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < u && i < s.len() ==>
            smaller_than(s, s[i], u)
    }
}

#[predicate]
fn all_larger(s: Seq<i32>, l: Int) -> bool {
    pearlite! {
        forall<i: Int> l <= i && i < s.len() ==>
            larger_than(s, s[i], l)
    }
}
#[predicate]
fn selection_sort_invariant(s: Seq<i32>, i: Int) -> bool {
    all_larger(s, i) && all_smaller(s, i)
}

#[predicate]
fn min_larger(s: Seq<i32>, u: Int, idx: Int) -> bool {
    pearlite! {forall<j: Int> 0 <= j && j < u ==> s[j] <= s[idx] }
}

#[requires(min_larger(@*v, @i, @i))]
#[requires(sorted_range(@v, 0, @i))]
#[requires(selection_sort_invariant(@v, @i))]
#[requires((@v).len() <= @0xffff_ffff_ffff_ffffusize)]
#[requires(0 <= @i && @i < (@v).len())]
#[ensures(min_larger(@v, @i, @result))]
#[ensures(forall<j: Int> @i <= j && j < (@v).len() ==> (@v)[@result] <= (@v)[j])] // min smaller
#[ensures(@i <= @result && @result < (@v).len())]
fn find_min(v: &Vec<i32>, i: usize) -> usize {
    let mut min = i;
    let mut j = i + 1;
    #[invariant(min_is_min, forall<k: Int> @i <= k && k < @j ==> (@v)[@min] <= (@v)[k])]
    #[invariant(j_bound, @i <= @j && @j <= (@v).len())]
    #[invariant(min_bound, @i <= @min && @min < (@v).len() && @min <= @j)]
    while j < v.len() {
        if v[j] < v[min] {
            min = j;
        }
        j += 1;
    }
    return min;
}

#[requires(0 <= @i && @i < (@v).len())]
#[requires(@i <= @min && @min < (@v).len())]
#[requires(sorted_range(@v, 0, @i))]
#[requires(selection_sort_invariant(@v, @i))]
#[requires(forall<j: Int> @i <= j && j < (@v).len() ==> (@v)[@min] <= (@v)[j])] // min smaller
#[ensures((@v)[@i] === (@^v)[@min] && (@v)[@min] === (@^v)[@i])] // i and min swapped
#[ensures(forall<j: Int> 0 <= j && j < (@v).len() && j != @i && j != @min ==> (@v)[j] === (@^v)[j])] // rest are unchanged
#[ensures((@^v).permutation_of(@v))]
#[ensures(selection_sort_invariant(@^v, @i+1))]
#[ensures(sorted_range(@^v, 0, @i+1))]
fn swap(v: &mut Vec<i32>, i: usize, min: usize) {
    v.swap(i, min);
}

#[ensures(sorted(@^v))]
#[ensures((@^v).permutation_of(@v))]
fn selection_sort(v: &mut Vec<i32>) {
    let mut i: usize = 0;
    let old_v = Ghost::record(&v);
    #[invariant(proph_const, ^v === ^@old_v)]
    #[invariant(permutation, (@*v).permutation_of(@*@old_v))]
    #[invariant(i_bound, 0 <= @i && @i <= (@v).len())]
    #[invariant(sorted, sorted_range(@v, 0, @i))]
    #[invariant(sort_inv, selection_sort_invariant(@v, @i))]
    while i < v.len() {
        let min = find_min(v, i);
        swap(v, i, min);
        i += 1;
    }
}
