// WHY3PROVE NOSPLIT CVC4
extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;

#[predicate]
fn sorted_range(s: Seq<u32>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i : Int, j : Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted(s: Seq<u32>) -> bool {
    sorted_range(s, 0, s.len())
}

#[requires((@arr).len() <= @usize::MAX)]
#[requires(sorted(@arr))]
#[ensures(forall<x:usize> result === Ok(x) ==> (@arr)[@x] === elem)]
#[ensures(forall<x:usize> result === Err(x) ==>
    forall<i:usize>  i < x ==> (@arr)[@i] <= elem)]
#[ensures(forall<x:usize> result === Err(x) ==>
    forall<i:usize> x < i && @i < (@arr).len() ==> elem < (@arr)[@i])]
fn binary_search(arr: &Vec<u32>, elem: u32) -> Result<usize, usize> {
    if arr.len() == 0 {
        return Err(0);
    }
    let mut size = arr.len();
    let mut base = 0;

    #[invariant(size_valid, 0 < @size && @size + @base <= (@arr).len())]
    #[invariant(lower_b, forall<i : usize> i < base ==> (@arr)[@i] <= elem)]
    #[invariant(lower_b, forall<i : usize> @base + @size < @i && @i < (@arr).len() ==> elem < (@arr)[@i])]
    while size > 1 {
        let half = size / 2;
        let mid = base + half;

        base = if arr[mid] > elem { base } else { mid };
        size -= half;
    }

    let cmp = arr[base];
    if cmp == elem {
        Ok(base)
    } else if cmp < elem {
        Err(base + 1)
    } else {
        Err(base)
    }
}
