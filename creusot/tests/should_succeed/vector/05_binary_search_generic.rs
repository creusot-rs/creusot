extern crate creusot_contracts;
use creusot_contracts::{std::cmp::Ord, *};
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
#[requires(sorted(@arr))]
#[ensures(forall<x:usize> result == Ok(x) ==> (@arr)[@x] == elem)]
#[ensures(forall<x:usize> result == Err(x) ==>
    forall<i:usize>  i < x ==> (@arr)[@i] <= elem)]
#[ensures(forall<x:usize> result == Err(x) ==>
    forall<i:usize> x <= i && @i < (@arr).len() ==> elem < (@arr)[@i])]
pub fn binary_search<T: Ord + OrdLogic>(arr: &Vec<T>, elem: T) -> Result<usize, usize> {
    if arr.len() == 0 {
        return Err(0);
    }
    let mut size: usize = arr.len();
    let mut base: usize = 0;

    #[invariant(size_valid, 0 < @size && @size + @base <= (@arr).len())]
    #[invariant(lower_b, forall<i : usize> i < base ==> (@arr)[@i] <= elem)]
    #[invariant(lower_b, forall<i : usize> @base + @size <= @i && @i < (@arr).len() ==> elem < (@arr)[@i])]
    while size > 1 {
        let half = size / 2;
        let mid = base + half;

        let x = &arr[mid];
        base = if x.gt(&elem) { base } else { mid };

        size -= half;
    }

    let cmp = &arr[base];

    match cmp.cmp(&elem) {
        Ordering::Equal => Ok(base),
        Ordering::Less => Err(base + 1),
        Ordering::Greater => Err(base),
    }
}
