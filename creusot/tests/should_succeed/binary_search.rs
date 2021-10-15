// SHOULD_SUCCEED: parse-print
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes, unsized_fn_params)]

// Here we prove the Rust stdlib implementation of binary search with a few changes
// 1. We use a List rather than a slice, this restriction is because Creusot cannot yet
//    axiomatize types, and should be lifted soon.
// 2. We monomorphize binary_search to u32, this is because we cannot handle trait constraints.
//    this restriction will be lifted but not in the immediate future. The best approach to handle
//    traits is not obvious.
// 3. Lists are restricted to size < 1,000,000 this is because of (1), since there is no upper
//    bound on the size of a list.
extern crate creusot_contracts;
use creusot_contracts::*;

trait MyEq {
    fn eq(&self, _: &Self) -> bool;
}

use std::cmp::Ordering;
trait Ord: MyEq {
    #[logic]
    fn cmp_log(self, _ : Self) -> std::cmp::Ordering;

    // #[logic]
    // fn le_log(self, o: Self) -> bool {
    //     use std::cmp::Ordering;
    //     pearlite! {
    //         self.cmp_log(o) === Ordering::Equal || self.cmp_log(o) === Ordering::Less
    //     }
    // }
    #[logic]
    fn le_log(self, o: Self) -> bool;

    fn le(&self, _: &Self) -> bool;
    fn lt(&self, _: &Self) -> bool;
    fn gt(&self, _: &Self) -> bool;

    // Coherence of the relations
    #[creusot::spec::pure]
    #[ensures(a.cmp_log(b) === Ordering::Equal || a.cmp_log(b) === Ordering::Less ==> a.le_log(b))]
    #[ensures(a.le_log(b) ==> a.cmp_log(b) === Ordering::Equal || a.cmp_log(b) === Ordering::Less)]
    fn le_cmp_coh(a: Self, b: Self);
}

struct Vec<T>(std::vec::Vec<T>);

impl<T: ?Sized> Model for Vec<T> {
    type ModelTy = Seq<T>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> Vec<T> {
    #[trusted]
    #[ensures(@result === (@*self).len())]
    fn len(&self) -> usize {
        self.0.len()
    }

    #[trusted]
    #[requires(@ix < (@*self).len())]
    #[ensures(*result === (@*self).index(@ix))]
    fn index(&self, ix: usize) -> &T {
        use std::ops::Index;
        self.0.index(ix)
    }
}

#[predicate]
fn sorted_range<T: Ord>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i : Int, j : Int> l <= i && i < j && j < u ==>
            s.index(i).le_log(s.index(j))
    }
}

#[predicate]
fn sorted<T: Ord>(s: Seq<T>) -> bool {
    sorted_range(s, 0, s.len())
}

#[requires((@arr).len() <= 1_000_000)]
#[requires(sorted(@arr))]
// #[ensures(forall<x:usize> result === Ok(x) ==> arr.get(@x) === Some(elem))]
// #[ensures(forall<x:usize> result === Err(x) ==>
//     forall<i:Int> 0 <= i && i < @x ==> arr.get_default(i, 0u32) < elem)]
// #[ensures(forall<x:usize> result === Err(x) ==>
//     forall<i:Int> @x < i && i < arr.len_logic() ==> elem < arr.get_default(i, 0u32))]
fn binary_search<T: Ord>(arr: &Vec<T>, elem: &T) -> Result<usize, usize> {
    if arr.len() == 0 {
        return Err(0);
    }
    let mut size = arr.len();
    let mut base = 0;

    #[invariant(size_valid, @size + @base <= (@arr).len())]
    #[invariant(in_interval, (@arr).index(@base).le_log(*elem) && elem.le_log((@arr).index(@base + @size)))]
    // #[invariant(in_interval, arr.get_default(@base, 0u32) <= elem &&
    //     elem <= arr.get_default(@base + @size, 0u32))]
    #[invariant(size_pos, size > 0usize)]
    while size > 1 {
        let half = size / 2;
        let mid = base + half;

        base = if arr.index(mid).gt(elem) { base } else { mid };
        size -= half;
    }

    let cmp = arr.index(base);
    if cmp.eq(elem) {
        Ok(base)
    } else if cmp.lt(elem) {
        Err(base + 1)
    } else {
        Err(base)
    }
}

fn main() {}
