#![feature(type_ascription)]
extern crate creusot_contracts;

use creusot_contracts::*;

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
#[ensures((@^v).permutation_of(@v))]
pub fn selection_sort<T: Ord + DeepModel>(v: &mut Vec<T>)
where
    T::DeepModelTy: OrdLogic,
{
    let mut i: usize = 0;
    let old_v = ghost! { v };
    #[invariant(proph_const, ^v == ^old_v.inner())]
    #[invariant(permutation, (@v).permutation_of(@old_v))]
    #[invariant(i_bound, @i <= (@v).len())]
    #[invariant(sorted, sorted_range(v.deep_model(), 0, @i))]
    #[invariant(partition, partition(v.deep_model(), @i))]
    while i < v.len() {
        let mut min = i;
        let mut j = i + 1;
        #[invariant(min_is_min, forall<k: Int> @i <= k && k < @j ==> v.deep_model()[@min] <= v.deep_model()[k])]
        #[invariant(j_bound, @i <= @j && @j <= (@v).len())]
        #[invariant(min_bound, @i <= @min && @min < @j)]
        while j < v.len() {
            if v[j] < v[min] {
                min = j;
            }
            j += 1;
        }
        v.swap(i, min);
        i += 1;
    }
}
