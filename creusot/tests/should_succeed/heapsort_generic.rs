#![feature(type_ascription)]
extern crate creusot_contracts;

use creusot_contracts::{
    logic::{Int, OrdLogic, Seq},
    *,
};

#[logic]
fn parent(i: Int) -> Int {
    (i + 1) / 2 - 1
}

#[predicate]
fn heap_frag<T: OrdLogic>(s: Seq<T>, start: Int, end: Int) -> bool {
    pearlite! { forall<i: Int> start <= parent(i) && i < end ==>
    s[i] <= s[parent(i)] }
}

#[logic]
#[requires(heap_frag(s, 0, end))]
#[requires(0 <= i && i < end)]
#[ensures(s[i] <= s[0])]
#[variant(i)]
fn heap_frag_max<T: OrdLogic>(s: Seq<T>, i: Int, end: Int) {
    if i > 0 {
        heap_frag_max(s, parent(i), end)
    }
}

#[requires(heap_frag(v.deep_model(), @start + 1, @end))]
#[requires(@start < @end)]
#[requires(@end <= (@v).len())]
#[ensures(heap_frag((^v).deep_model(), @start, @end))]
#[ensures((@^v).permutation_of(@v))]
#[ensures(forall<i: Int> 0 <= i && i < @start || @end <= i && i < (@v).len()
                      ==> (@v)[i] == (@^v)[i])]
#[ensures(forall<m: T::DeepModelTy>
          (forall<j: Int> @start <= j && j < @end ==> v.deep_model()[j] <= m) ==>
          forall<j: Int> @start <= j && j < @end ==> (^v).deep_model()[j] <= m)]
fn sift_down<T: Ord + DeepModel>(v: &mut Vec<T>, start: usize, end: usize)
where
    T::DeepModelTy: OrdLogic,
{
    let old_v = ghost! { v };
    let mut i = start;

    #[invariant(permutation, (@v).permutation_of(@old_v))]
    #[invariant(i_bounds, @start <= @i && @i < @end)]
    #[invariant(unchanged, forall<j: Int> 0 <= j && j < @start || @end <= j && j < (@v).len()
                              ==> (@old_v)[j] == (@v)[j])]
    #[invariant(keep_bound, forall<m: T::DeepModelTy>
          (forall<j: Int> @start <= j && j < @end ==> old_v.deep_model()[j] <= m) ==>
          forall<j: Int> @start <= j && j < @end ==> v.deep_model()[j] <= m)]
    #[invariant(heap, forall<j: Int> @start <= parent(j) && j < @end && @i != parent(j) ==>
            v.deep_model()[j] <= v.deep_model()[parent(j)])]
    #[invariant(hole_left,  {let c = 2*@i+1; c < @end && @start <= parent(@i) ==> v.deep_model()[c] <= v.deep_model()[parent(parent(c))]})]
    #[invariant(hole_right, {let c = 2*@i+2; c < @end && @start <= parent(@i) ==> v.deep_model()[c] <= v.deep_model()[parent(parent(c))]})]
    loop {
        if i >= end / 2 {
            return;
        }

        let mut child = 2 * i + 1;
        if child + 1 < end && v[child] < v[child + 1] {
            child += 1
        }
        if v[child] <= v[i] {
            return;
        }
        v.swap(i, child);
        i = child
    }
}

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

#[requires((@v).len() < @std::usize::MAX/2)]
#[ensures(sorted((^v).deep_model()))]
#[ensures((@^v).permutation_of(@v))]
pub fn heap_sort<T: Ord + DeepModel>(v: &mut Vec<T>)
where
    T::DeepModelTy: OrdLogic,
{
    let old_v = ghost! { v };

    let mut start = v.len() / 2;
    #[invariant(permutation, (@v).permutation_of(@old_v))]
    #[invariant(heap, heap_frag(v.deep_model(), @start, (@v).len()))]
    #[invariant(start_bound, @start <= (@v).len()/2)]
    while start > 0 {
        start -= 1;
        sift_down(v, start, v.len());
    }

    let mut end = v.len();
    #[invariant(end_bound, @end <= (@v).len())]
    #[invariant(permutation, (@v).permutation_of(@old_v))]
    #[invariant(heap, heap_frag(v.deep_model(), 0, @end))]
    #[invariant(sorted, sorted_range(v.deep_model(), @end, (@v).len()))]
    #[invariant(heap_le, forall<i : Int, j : Int> 0 <= i && i < @end && @end <= j && j < (@v).len() ==>
                            v.deep_model()[i] <= v.deep_model()[j])]
    while end > 1 {
        end -= 1;
        v.swap(0, end);
        proof_assert! {
            heap_frag_max(v.deep_model(), 0/*dummy*/, @end);
            forall<i : Int, j : Int> 0 <= i && i < @end && @end <= j && j < (@v).len() ==>
                        v.deep_model()[i] <= v.deep_model()[j]
        };
        sift_down(v, 0, end);
    }
}
