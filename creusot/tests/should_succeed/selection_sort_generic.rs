// UNSTABLE
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

#[ensures(sorted((^v).eq_model()))]
#[ensures((^v)@.permutation_of(v@))]
pub fn selection_sort<T: Ord + EqModel>(v: &mut Vec<T>)
where
    T::EqModelTy: OrdLogic,
{
    let old_v = snapshot! { v };
    #[invariant(^v == ^*old_v)]
    #[invariant(v@.permutation_of(old_v@))]
    #[invariant(sorted_range(v.eq_model(), 0, produced.len()))]
    #[invariant(partition(v.eq_model(), produced.len()))]
    for i in 0..v.len() {
        let mut min = i;

        #[invariant(forall<k: Int> i@ <= k && k < produced.len() + i@ + 1 ==> v.eq_model()[min@] <= v.eq_model()[k])]
        #[invariant(i@ <= min@ && min@ < produced.len() + i@ + 1)]
        for j in (i + 1)..v.len() {
            if v[j] < v[min] {
                min = j;
            }
        }
        v.swap(i, min);
        proof_assert! { let i = produced.len(); forall<k1 : Int, k2: Int> 0 <= k1 && k1 < i && i <= k2 && k2 < v.eq_model
        ().len() ==> v.eq_model()[k1] <= v.eq_model()[k2] };
    }
}
