#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]
#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::*;

struct Vec<T>(std::vec::Vec<T>);

pub struct Ghost<T>(*mut T)
where
    T: ?Sized;

impl<T> Model for Ghost<T> {
    type ModelTy = T;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

impl<T> Ghost<T> {
    #[trusted]
    #[ensures(@result === *a)]
    fn record(a: &T) -> Ghost<T> {
        panic!()
    }
}

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

    #[trusted]
    #[ensures((@^self).index(@i) === (@*self).index(@j))]
    #[ensures((@^self).index(@j) === (@*self).index(@i))]
    #[ensures(forall<k : Int> 0 <= k && k <= (@^self).len() && @i != k && @j != k ==>
        (@^self).index(k) === (@*self).index(k)
    )]
    #[ensures((@^self).len() === (@*self).len())]
    fn swap(&mut self, i: usize, j: usize) {
        self.0.swap(i, j)
    }
}

trait Ord {
    #[logic]
    fn le_log(self, _: Self) -> bool;

    #[ensures(result === self.le_log(*o))]
    fn le(&self, o: &Self) -> bool;

    #[creusot::spec::pure]
    #[requires(a.le_log(*b) && b.le_log(*c))]
    #[ensures(a.le_log(*c))]
    fn trans(a: &Self, b: &Self, c: &Self);
}

#[predicate]
fn sorted_range<T: Ord>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i : Int, j : Int> l <= i && i < j && j < u ==> s.index(i).le_log(s.index(j))
    }
}

#[predicate]
fn sorted<T: Ord>(s: Seq<T>) -> bool {
    sorted_range(s, 0, s.len())
}

#[ensures(sorted(@^v))]
#[ensures((@^v).permutation_of(@*v))]
fn gnome_sort<T: Ord>(v: &mut Vec<T>) {
    let old_v = Ghost::record(&v);

    let mut i = 0;
    #[invariant(sorted, sorted_range(@v, 0, @i))]
    #[invariant(proph_const, ^v === ^@old_v)]
    #[invariant(in_len, @i <= (@*v).len())]
    #[invariant(permutation, (@*v).permutation_of(@*@old_v))]
    while i < v.len() {
        if i == 0 || v.index(i - 1).le(v.index(i)) {
            i += 1;
        } else {
            v.swap(i - 1, i);
            i -= 1;
        }
    }
}
