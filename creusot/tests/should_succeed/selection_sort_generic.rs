#![feature(type_ascription)]
extern crate creusot_contracts;

use creusot_contracts::{
    logic::{Int, OrdLogic, Seq},
    *,
};

#[predicate]
fn sorted_range<T: OrdLogic>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i: Int, j :Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted<T: OrdLogic>(s: Seq<T>) -> bool {
    pearlite! {
        sorted_range(s, 0, s.len())
    }
}

#[predicate]
fn partition<T: OrdLogic>(v: Seq<T>, i: Int) -> bool {
    pearlite! { forall<k1 : Int, k2: Int> 0 <= k1 && k1 < i && i <= k2 && k2 < v.len() ==> v[k1] <= v[k2]}
}

#[ensures(sorted((^v).deep_model()))]
#[ensures(((^v)@).permutation_of(v@))]
pub fn selection_sort<T: Ord + DeepModel>(v: &mut Vec<T>)
where
    T::DeepModelTy: OrdLogic,
{
    let old_v = ghost! { v };
    #[invariant(permutation, v@.permutation_of(old_v@))]
    #[invariant(sorted, sorted_range(v.deep_model(), 0, produced.len()))]
    #[invariant(partition, partition(v.deep_model(), produced.len()))]
    for i in 0..v.len() {
        let mut min = i;
        #[invariant(min_is_min, forall<k: Int> i@ <= k && k < produced.len() + i@ + 1 ==> v.deep_model()[min@] <= v.deep_model()[k])]
        #[invariant(min_bound, i@ <= min@ && min@ < produced.len() + i@ + 1)]
        for j in (i + 1)..v.len() {
            if v[j] < v[min] {
                min = j;
            }
        }
        v.swap(i, min);
    }
}
