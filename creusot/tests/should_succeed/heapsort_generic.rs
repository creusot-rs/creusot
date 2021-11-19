#![feature(type_ascription)]
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

#[logic]
fn left(i: Int) -> Int {
    2 * i + 1
}

#[logic]
fn right(i: Int) -> Int {
    2 * i + 2
}

#[predicate]
fn heap_frag<T: OrdLogic>(s: Seq<T>, start: Int, end: Int) -> bool {
    pearlite! { forall<i: Int> start <= i ==>
        ((left(i) < end) ==> s[left(i)] <= s[i])
    &&  ((right(i) < end) ==> s[right(i)] <= s[i]) }
}

#[logic]
#[requires(heap_frag(s, 0, end))]
#[requires(0 <= i && i < end)]
#[ensures(s[i] <= s[0])]
#[variant(i)]
fn heap_frag_max<T: OrdLogic>(s: Seq<T>, i: Int, end: Int) {
    if i > 0 {
        heap_frag_max(s, (i + 1) / 2 - 1, end)
    }
}

#[requires(heap_frag(@v, @start + 1, @end))]
#[requires(@start < @end)]
#[requires(@end <= (@v).len())]
#[ensures(heap_frag(@^v, @start, @end))]
#[ensures((@^v).permutation_of(@v))]
#[ensures(forall<i: Int> 0 <= i && i < @start || @end <= i && i < (@v).len()
                      ==> (@v)[i] === (@^v)[i])]
#[ensures(forall<m: T>
          (forall<j: Int> @start <= j && j < @end ==> (@v)[j] <= m) ==>
          forall<j: Int> @start <= j && j < @end ==> (@^v)[j] <= m)]
fn shift_down<T: Ord>(v: &mut Vec<T>, start: usize, end: usize) {
    let old_v = Ghost::record(&v);
    let mut i = start;

    #[invariant(proph_const, ^v === ^@old_v)]
    #[invariant(permutation, (@v).permutation_of(@@old_v))]
    #[invariant(i_bounds, @start <= @i && @i < @end)]
    #[invariant(unchanged, forall<j: Int> 0 <= j && j < @start || @end <= j && j < (@v).len()
                              ==> (@@old_v)[j] === (@v)[j])]
    #[invariant(keep_bound, forall<m: T>
          (forall<j: Int> @start <= j && j < @end ==> (@@old_v)[j] <= m) ==>
          forall<j: Int> @start <= j && j < @end ==> (@v)[j] <= m)]
    #[invariant(heap, forall<j: Int> @start <= j && !(@i === j) ==>
            ((left(j) < @end) ==> (@v)[left(j)] <= (@v)[j])
        &&  ((right(j) < @end) ==> (@v)[right(j)] <= (@v)[j]))]
    #[invariant(hole_left,  ((left(@i) < @end) && @start < (@i+1)/2 ==> (@v)[left(@i)] <= (@v)[(@i+1)/2-1]))]
    #[invariant(hole_right, ((right(@i) < @end) && @start < (@i+1)/2 ==> (@v)[right(@i)] <= (@v)[(@i+1)/2-1]))]
    loop {
        if i >= usize::MAX / 2 {
            return;
        }

        let mut child = 2 * i + 1;
        if child >= end {
            return;
        }
        if child + 1 < end && v[child].lt(&v[child + 1]) {
            child += 1
        }
        if v[child].le(&v[i]) {
            return;
        }
        v.swap(i, child);
        i = child
    }
}

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

#[requires((@v).len() < @std::usize::MAX/2)]
#[ensures(sorted(@^v))]
#[ensures((@^v).permutation_of(@v))]
fn heap_sort<T: Ord>(v: &mut Vec<T>) {
    let old_v = Ghost::record(&v);

    let mut start = v.len() / 2;
    #[invariant(permutation, (@v).permutation_of(@@old_v))]
    #[invariant(proph_const, ^v === ^@old_v)]
    #[invariant(heap, heap_frag(@v, @start, (@v).len()))]
    #[invariant(start_bound, @start <= (@v).len()/2)]
    while start > 0 {
        start -= 1;
        shift_down(v, start, v.len());
    }

    let mut end = v.len();
    #[invariant(end_bound, @end <= (@v).len())]
    #[invariant(permutation, (@v).permutation_of(@@old_v))]
    #[invariant(proph_const, ^v === ^@old_v)]
    #[invariant(heap, heap_frag(@v, 0, @end))]
    #[invariant(sorted, sorted_range(@v, @end, (@v).len()))]
    #[invariant(heap_le, forall<i : Int, j : Int> 0 <= i && i < @end && @end <= j && j < (@v).len() ==>
                            (@v)[i] <= (@v)[j])]
    while end > 1 {
        proof_assert! {{heap_frag_max(@v, 0/*dummy*/, @end); true}}
        end -= 1;
        v.swap(0, end);
        shift_down(v, 0, end);
    }
}
