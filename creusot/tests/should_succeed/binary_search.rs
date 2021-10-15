// SHOULD_SUCCEED: parse-print
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

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

enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

impl<T> WellFounded for List<T> {}
use List::*;

trait MyEq {
    fn eq(&self, _: &Self) -> bool;
}

trait MyOrd: MyEq {
    #[logic]
    fn le_logic(self, _: Self) -> bool;
    fn le(&self, _: &Self) -> bool;
    fn lt(&self, _: &Self) -> bool;
    fn gt(&self, _: &Self) -> bool;
}

impl<T> List<T> {
    #[pure]
    #[ensures(result >= 0)]
    #[variant(self)]
    fn len_logic(self) -> Int {
        match self {
            Cons(_, ls) => Int::from(1) + ls.len_logic(),
            Nil => 0.into(),
        }
    }

    #[logic]
    fn get(self, ix: Int) -> Option<T> {
        match self {
            Cons(t, ls) => {
                if ix == 0 {
                    Some(t)
                } else {
                    ls.get(ix - 1)
                }
            }
            Nil => None,
        }
    }

    #[pure]
    #[requires(self.len_logic() > ix.into())]
    #[variant(*self)]
    fn index_pure(&self, ix: usize) -> &T {
        match self {
            Cons(t, ls) => {
                if ix == 0 {
                    t
                } else {
                    ls.index_pure(ix - 1)
                }
            }
            Nil => unreachable!("OMG"),
        }
    }
}

impl<T> List<T> {
    #[logic]
    fn get_default(self, ix: Int, def: T) -> T {
        match self.get(ix) {
            Some(v) => v,
            None => def,
        }
    }

    #[logic]
    fn is_sorted(self) -> bool
    where
        T: MyOrd,
    {
        pearlite! {
        forall<x1 : Int, x2 : Int> x1 <= x2 ==>
            match (self.get(x1), self.get(x2)) {
                // curious: if we put a & next to v2, parsing breaks?!
                (Some(v1), Some(v2)) => v1.le_logic(v2),
                (None, None) => true,
                _ => false
            }
        }
    }

    #[requires(@ix < self.len_logic())]
    #[ensures(Some(*result) === self.get(@ix))]
    fn index(&self, mut ix: usize) -> &T {
        let orig_ix = ix;
        let mut l = self;

        #[invariant(ix_valid, @ix < l.len_logic())]
        #[invariant(res_get, self.get(@orig_ix) === l.get(@ix))]
        while let Cons(t, ls) = l {
            if ix > 0 {
                l = &*ls;
                ix -= 1;
            } else {
                return t;
            }
        }
        std::process::abort()
    }

    // Temporary until support for usize::MAX is added
    #[requires(self.len_logic() <= 1_000_000)]
    #[ensures(result >= 0usize)]
    #[ensures(@result == self.len_logic())]
    fn len(&self) -> usize {
        let mut len = 0;
        let mut l = self;
        #[invariant(len_valid, @len + l.len_logic() == self.len_logic())]
        while let Cons(_, ls) = l {
            len += 1;
            l = ls;
        }
        len
    }
}

#[requires(arr.len_logic() <= 1_000_000)]
#[requires(arr.is_sorted())]
// #[ensures(forall<x:usize> result === Ok(x) ==> arr.get(@x) === Some(elem))]
// #[ensures(forall<x:usize> result === Err(x) ==>
//     forall<i:Int> 0 <= i && i < @x ==> arr.get_default(i, 0u32) < elem)]
// #[ensures(forall<x:usize> result === Err(x) ==>
//     forall<i:Int> @x < i && i < arr.len_logic() ==> elem < arr.get_default(i, 0u32))]
fn binary_search<T: MyOrd>(arr: &List<T>, elem: &T) -> Result<usize, usize> {
    if arr.len() == 0 {
        return Err(0);
    }
    let mut size = arr.len();
    let mut base = 0;

    #[invariant(size_valid, @size + @base <= arr.len_logic())]
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
