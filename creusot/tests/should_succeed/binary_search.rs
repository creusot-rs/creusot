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
use List::*;

logic! {
fn len_logic<T>(l : List<T>) -> Int {
    match l {
        Cons(_, ls) => 1 + len_logic(*ls),
        Nil => 0,
    }
}
}

logic! {
fn get<T>(l : List<T>, ix : Int) -> Option<T> {
    match l {
        Cons(t, ls) => {
            if ix == 0 {
                Some(t)
            } else {
                get(*ls, ix - 1)
            }
        }
        Nil => None,
    }
}
}

impl<T> List<T> {
    #[requires(Int::from(ix) < len_logic(*self))]
    #[ensures(equal(Some(*result), get(*self, Int::from(ix))))]
    fn index(&self, mut ix: usize) -> &T {
        let orig_ix = ix;
        let mut l = self;

        #[invariant(ix_valid, Int::from(ix) < len_logic(*l))]
        #[invariant(res_get, equal(get(*self, Int::from(orig_ix)), get(*l, Int::from(ix))))]
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
    #[requires(len_logic(*self) <= Int::from(1_000_000))]
    #[ensures(result >= 0usize)]
    #[ensures(Int::from(result) == len_logic(*self))]
    fn len(&self) -> usize {
        let mut len = 0;
        let mut l = self;
        #[invariant(len_valid, Int::from(len) + len_logic(*l) == len_logic(*self))]
        while let Cons(_, ls) = l {
            len += 1;
            l = ls;
        }
        len
    }
}

logic! {
    fn is_sorted(l : List<u32>) -> bool { {
        forall<x1 : Int, x2 : Int> x1 <= x2 ==>
            match (get(l, x1), get(l, x2)) {
                (Some(v1), Some(v2)) => v1 <= v2,
                (None, None) => true,
                _ => false
            }
        }
    }
}

logic! {
    fn get_default<T>(l : List<T>, ix: Int, def: T) -> T {
        match get(l, ix) {
            Some(v) => v,
            None => def,
        }
    }
}

#[requires(len_logic(*arr) <= Int::from(1_000_000))]
#[requires(is_sorted(*arr))]
#[ensures(forall<x:usize> equal(result, Ok(x)) ==> equal(get(*arr, Int::from(x)), Some(elem)))]
#[ensures(forall<x:usize> equal(result, Err(x)) ==>
    forall<i:Int> 0 <= i && i < Int::from(x) ==> get_default(*arr, i, 0u32) < elem)]
#[ensures(forall<x:usize> equal(result, Err(x)) ==>
    forall<i:Int> Int::from(x) < i && i < len_logic(*arr) ==> elem < get_default(*arr, i, 0u32))]
fn binary_search(arr: &List<u32>, elem: u32) -> Result<usize, usize> {
    if arr.len() == 0 {
        return Err(0);
    }
    let mut size = arr.len();
    let mut base = 0;

    #[invariant(size_valid, Int::from(size) + Int::from(base) <= len_logic(*arr))]
    #[invariant(in_interval, get_default(*arr, Int::from(base), 0u32) <= elem &&
        elem <= get_default(*arr, Int::from(base) + Int::from(size), 0u32))]
    #[invariant(size_pos, size > 0usize)]
    while size > 1 {
        let half = size / 2;
        let mid = base + half;

        base = if *arr.index(mid) > elem { base } else { mid };
        size -= half;
    }

    let cmp = *arr.index(base);
    if cmp == elem {
        Ok(base)
    } else if cmp < elem {
        Err(base + 1)
    } else {
        Err(base)
    }
}

fn main() {}
