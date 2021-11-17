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


//#[ensures(sorted(@^v))]
#[requires((@v).len() < @std::usize::MAX/2)]
#[ensures((@^v).permutation_of(@v))]
fn heap_sort<T: Ord>(v: &mut Vec<T>) {
    let old_v = Ghost::record(&v);
    let len = v.len();
    let mut start = len / 2;
    // Create heap
    #[invariant(start_inv, @start <= (@len)/2)]
    #[invariant(permutation, (@v).permutation_of(@@old_v))]
    #[invariant(proph_const, ^v === ^@old_v)]
    while start > 0 {
        start -= 1;
        shift_down(v, start, len - 1);
    }

    let mut end = len;
    #[invariant(end_inv, @end <= @len)]
    #[invariant(permutation, (@v).permutation_of(@@old_v))]
    #[invariant(proph_const, ^v === ^@old_v)]
    while end > 1 {
        end -= 1;
        let zero = 0;
        v.swap(zero, end);
        shift_down(v, zero, end - 1);
    }
}

#[logic]
fn left(i : Int) -> Int {
    2 * i + 1
}

#[logic]
fn right(i : Int) -> Int {
    2 * i + 2
}

#[predicate]
// #[requireS(i >= 0)]
fn heap_frag<T : OrdLogic>(s: Seq<T>, i: Int, u: Int) -> bool {
    pearlite! {
        forall<j : Int> i <= j && j < u ==>
            ((left(j) < u) ==> s[j] >= s[left(j)])
        &&  ((right(j) < u) ==> s[j] >= s[right(j)])
    }
    // pearlite! {
    //     u <= s.len() &&
    //     if i >= u {
    //         true
    //     } else {
    //         s[i] >= s[left(i)] && s[i] >= s[right(i)] && heap_frag(s, left(i), u) && heap_frag(s, right(i), u)
    //     }
    // }
}

#[requires(heap_frag(@v, @start + 1, @end))]
// #[requires(heap_frag(@v, right(@start), @end))]
#[ensures(heap_frag(@^v, @start, @end))]
// #[requires(@start <= (@v).len())]
#[requires(@end <= (@v).len())]
#[ensures((@^v)[@start] >= (@v)[@start])]
#[ensures((@^v)[@start] === (@v)[left(@start)] || (@^v)[@start] === (@v)[right(@start)] || (@^v)[@start] === (@v)[@start])]
#[ensures(forall<i : Int> 0 <= i && i < @start || @end <= i && i < (@v).len() ==> (@v)[i] === (@^v)[i])]
#[ensures((@^v).permutation_of(@v))]
fn shift_down<T: Ord>(v: &mut Vec<T>, start: usize, end: usize) {
    if start >= usize::MAX / 2 {
        return;
    }

    let mut child = start * 2 + 1;

    if child >= end {
        return;
    } else {
        let mut swap = start;
        if v[swap].lt(&v[child]) {
            swap = child;
        }
        if child + 1 < end && v[swap].lt(&v[child + 1]) {
            swap = child + 1;
        }
        if swap == start {
            proof_assert! {((left(@start) < @end) ==> (@v)[@start] >= (@v)[left(@start)])
                &&  ((right(@start) < @end) ==> (@v)[@start] >= (@v)[right(@start)]) };
            // proof_assert! { heap_frag(@v, right(@start), @end) };
            // proof_assert! { heap_frag(@v, left(@start), @end) };
            // proof_assert! { (@v)[@start] >= (@v)[left(@start)] };
            // proof_assert! { (@v)[@start] >= (@v)[right(@start)] };
            return;
        } else {
            v.swap(start, swap);
            shift_down(v, swap, end)
        }
    }

}

fn main() {}
