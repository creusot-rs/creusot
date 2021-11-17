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
    #[invariant(v_len, (@v).len() < @std::usize::MAX/2)]
    #[invariant(start_inv, 0 <= @start && @start <= (@len)/2)]
    #[invariant(permutation, (@*v).permutation_of(@*@old_v))]
    #[invariant(proph_const, ^v === ^@old_v)]
    while start > 0 {
        start -= 1;
        shift_down(v, start, len - 1);
    }

    let mut end = len;
    #[invariant(v_len, (@v).len() < @std::usize::MAX/2)]
    #[invariant(end_inv, 0 <= @end && @end <= @len)]
    #[invariant(permutation, (@*v).permutation_of(@*@old_v))]
    #[invariant(proph_const, ^v === ^@old_v)]
    while end > 1 {
        end -= 1;
        let zero = 0;
        v.swap(zero, end);
        shift_down(v, zero, end - 1);
    }
}

#[requires((@v).len() < @std::usize::MAX/2)]
#[ensures((@^v).permutation_of(@v))]
#[requires(0 <= @start && @start < (@v).len()/2)]
#[requires(0 <= @end && @end < (@v).len())]
fn shift_down<T: Ord>(v: &mut Vec<T>, start: usize, end: usize) {
    let old_v = Ghost::record(&v);
    let mut root = start;
    let mut continue_loop = true;
    #[invariant(v_len, (@v).len() < @std::usize::MAX/2)]
    #[invariant(root_inv, 0 <= @root && @root <= (@v).len())]
    #[invariant(end_inv, 0 <= @end && @end <= (@v).len())]
    #[invariant(permutation, (@*v).permutation_of(@*@old_v))]
    #[invariant(proph_const, ^v === ^@old_v)]
    while continue_loop {
        let mut child = root * 2 + 1;
        if child > end {
            continue_loop = false;
        } else {
            if child + 1 <= end && v[child].lt(&v[child + 1]) {
                child += 1;
            }
            if v[root].lt(&v[child]) {
                v.swap(root, child);
                root = child
            } else {
                continue_loop = false;
            }
        }
    }
}

fn main() {}
