#![allow(dead_code)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[predicate]
fn sorted_range<T: OrdLogic>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i, j> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted<T: OrdLogic>(s: Seq<T>) -> bool {
    pearlite! {
        sorted_range(s, 0, s.len())
    }
}

#[ensures(array@.permutation_of((^array)@))]
#[ensures(sorted((^array)@))]
pub fn insertion_sort(array: &mut [i32]) {
    let original = snapshot!(array); // remember the original value
    let n = array.len();
    #[invariant(sorted_range(array@, 0, produced.len() + 1))]
    #[invariant(array@.len() == n@)]
    #[invariant(original@.permutation_of(array@))]
    for i in 1..n {
        let mut j = i;
        #[invariant(j <= i)]
        #[invariant(array@.len() == n@)]
        #[invariant(original@.permutation_of(array@))]
        #[invariant(forall<a, b> 0 <= a && a <= b && b <= i@ ==> a != j@ ==> b != j@ ==> array[a] <= array[b])]
        #[invariant(forall<a> j@ + 1 <= a && a <= i@ ==> array[j] < array[a])]
        while j > 0 {
            if array[j - 1] > array[j] {
                array.swap(j - 1, j);
            } else {
                break;
            }
            j -= 1;
        }
    }

    proof_assert!(sorted_range(array@, 0, array@.len()));
}
