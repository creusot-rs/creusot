// WHY3PROVE CVC4
#![feature(unsized_fn_params)]
extern crate creusot_contracts;
use creusot_contracts::std::*;
use creusot_contracts::*;
use std::cmp::Ordering;
pub trait Ord {
    #[logic]
    fn cmp_log(self, _: Self) -> Ordering;

    #[ensures(result === self.cmp_log(*o))]
    fn cmp(&self, o: &Self) -> Ordering;

    #[predicate]
    fn le_log(self, o: Self) -> bool {
        pearlite! { !(self.cmp_log(o) === Ordering::Greater) }
    }

    #[ensures(result === self.le_log(*o))]
    fn le(&self, o: &Self) -> bool {
        match self.cmp(o) {
            Ordering::Greater => false,
            _ => true,
        }
    }

    #[predicate]
    fn ge_log(self, o: Self) -> bool {
        match self.cmp_log(o) {
            Ordering::Less => false,
            _ => true,
        }
    }

    #[ensures(result === self.ge_log(*o))]
    fn ge(&self, o: &Self) -> bool {
        match self.cmp(o) {
            Ordering::Less => false,
            _ => true,
        }
    }

    #[predicate]
    fn gt_log(self, o: Self) -> bool {
        match self.cmp_log(o) {
            Ordering::Greater => true,
            _ => false,
        }
    }

    #[ensures(result === self.gt_log(*o))]
    fn gt(&self, o: &Self) -> bool {
        match self.cmp(o) {
            Ordering::Greater => true,
            _ => false,
        }
    }

    #[predicate]
    fn lt_log(self, o: Self) -> bool {
        match self.cmp_log(o) {
            Ordering::Less => true,
            _ => false,
        }
    }

    #[ensures(result === self.lt_log(*o))]
    fn lt(&self, o: &Self) -> bool {
        match self.cmp(o) {
            Ordering::Less => true,
            _ => false,
        }
    }

    #[logic]
    #[ensures(x.cmp_log(y) === Ordering::Equal ==> x === y)]
    fn eq_is_eq(x: Self, y: Self);

    #[logic]
    #[ensures(x.cmp_log(x) === Ordering::Equal)]
    fn refl(x: Self);

    #[logic]
    #[requires(x.cmp_log(y) === o)]
    #[requires(y.cmp_log(z) === o)]
    #[ensures(x.cmp_log(z) === o)]
    fn trans(x: Self, y: Self, z: Self, o: Ordering);

    #[logic]
    #[requires(x.cmp_log(y) === Ordering::Less)]
    #[ensures(y.cmp_log(x) === Ordering::Greater)]
    fn antisym1(x: Self, y: Self);

    #[logic]
    #[requires(x.cmp_log(y) === Ordering::Greater)]
    #[ensures(y.cmp_log(x) === Ordering::Less)]
    fn antisym2(x: Self, y: Self);

    #[logic]
    #[requires(x.cmp_log(y) === Ordering::Equal)]
    #[ensures(y.cmp_log(x) === Ordering::Equal)]
    fn symmetry(x: Self, y: Self);
}

#[predicate]
fn sorted_range<T: Ord>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i : Int, j : Int> l <= i && i <= j && j < u ==> s[i].le_log(s[j])
    }
}

#[predicate]
fn sorted<T: Ord>(s: Seq<T>) -> bool {
    sorted_range(s, 0, s.len())
}

#[requires((@arr).len() <= @usize::MAX)]
#[requires(sorted(@arr))]
#[ensures(forall<x:usize> result === Ok(x) ==> (@arr)[@x] === elem)]
#[ensures(forall<x:usize> result === Err(x) ==>
    forall<i:usize>  i < x ==> (@arr)[@i].le_log(elem))]
#[ensures(forall<x:usize> result === Err(x) ==>
    forall<i:usize> x <= i && @i < (@arr).len() ==> elem.lt_log((@arr)[@i]))]
fn binary_search<T: Ord>(arr: &Vec<T>, elem: T) -> Result<usize, usize> {
    if arr.len() == 0 {
        return Err(0);
    }
    let mut size: usize = arr.len();
    let mut base: usize = 0;

    proof_assert! { {Ord::trans(elem, elem, elem, Ordering::Equal); true} };
    proof_assert! { {Ord::antisym1(elem, elem); true} };
    proof_assert! { {Ord::antisym2(elem, elem); true} };
    proof_assert! { {Ord::symmetry(elem, elem); true} };
    proof_assert! { {Ord::eq_is_eq(elem, elem); true} };

    #[invariant(size_valid, 0 < @size && @size + @base <= (@arr).len())]
    #[invariant(lower_b, forall<i : usize> i < base ==> (@arr)[@i].le_log(elem))]
    #[invariant(lower_b, forall<i : usize> @base + @size <= @i && @i < (@arr).len() ==> elem.lt_log((@arr)[@i]))]
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
