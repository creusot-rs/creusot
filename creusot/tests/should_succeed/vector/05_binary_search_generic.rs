extern crate creusot_contracts;
use creusot_contracts::*;
use std::cmp::Ordering;

#[predicate]
fn sorted_range<T: OrdLogic>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i : Int, j : Int> l <= i && i <= j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted<T: OrdLogic>(s: Seq<T>) -> bool {
    sorted_range(s, 0, s.len())
}

#[requires((@arr).len() <= @usize::MAX)]
#[requires(sorted(arr.deep_model()))]
#[ensures(forall<x:usize> result == Ok(x) ==> arr.deep_model()[@x] == elem.deep_model())]
#[ensures(forall<x:usize> result == Err(x) ==>
    forall<i:usize>  i < x ==> arr.deep_model()[@i] <= elem.deep_model())]
#[ensures(forall<x:usize> result == Err(x) ==>
    forall<i:usize> x <= i && @i < (@arr).len() ==> elem.deep_model() < arr.deep_model()[@i])]
pub fn binary_search<T: Ord + DeepModel>(arr: &Vec<T>, elem: T) -> Result<usize, usize>
where
    T::DeepModelTy: OrdLogic,
{
    if arr.len() == 0 {
        return Err(0);
    }
    let mut size: usize = arr.len();
    let mut base: usize = 0;

    #[invariant(size_valid, 0 < @size && @size + @base <= (@arr).len())]
    #[invariant(lower_b, forall<i : usize> i < base ==> arr.deep_model()[@i] <= elem.deep_model())]
    #[invariant(lower_b, forall<i : usize> @base + @size <= @i && @i < (@arr).len() ==> elem.deep_model() < arr.deep_model()[@i])]
    while size > 1 {
        let half = size / 2;
        let mid = base + half;

        base = if arr[mid] > elem { base } else { mid };

        size -= half;
    }

    let cmp = &arr[base];

    match cmp.cmp(&elem) {
        Ordering::Equal => Ok(base),
        Ordering::Less => Err(base + 1),
        Ordering::Greater => Err(base),
    }
}
