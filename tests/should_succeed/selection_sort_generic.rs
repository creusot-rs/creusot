extern crate creusot_contracts;

use creusot_contracts::{
    logic::{Int, OrdLogic, Seq},
    *,
};

#[logic]
#[open]
pub fn sorted_range<T: OrdLogic>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i, j> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[logic]
#[open]
pub fn sorted<T: OrdLogic>(s: Seq<T>) -> bool {
    pearlite! {
        sorted_range(s, 0, s.len())
    }
}

#[logic]
fn partition<T: OrdLogic>(v: Seq<T>, i: Int) -> bool {
    pearlite! { forall<k1, k2> 0 <= k1 && k1 < i && i <= k2 && k2 < v.len() ==> v[k1] <= v[k2]}
}

#[ensures(sorted((^v).deep_model()))]
#[ensures((^v)@.permutation_of(v@))]
pub fn selection_sort<T: Ord + DeepModel>(v: &mut Vec<T>)
where
    T::DeepModelTy: OrdLogic,
{
    let old_v = snapshot! { v };

    #[invariant(v@.permutation_of(old_v@))]
    #[invariant(sorted_range(v.deep_model(), 0, produced.len()))]
    #[invariant(partition(v.deep_model(), produced.len()))]
    for i in 0..v.len() {
        let mut min = i;

        #[invariant(forall<k> i@ <= k && k < produced.len() + i@ + 1 ==> v.deep_model()[min@] <= v.deep_model()[k])]
        #[invariant(i@ <= min@ && min@ < produced.len() + i@ + 1)]
        for j in (i + 1)..v.len() {
            if v[j] < v[min] {
                min = j;
            }
        }
        v.swap(i, min);
        proof_assert! { let i = produced.len(); forall<k1, k2> 0 <= k1 && k1 < i && i <= k2 && k2 < v.deep_model
        ().len() ==> v.deep_model()[k1] <= v.deep_model()[k2] };
    }
}
