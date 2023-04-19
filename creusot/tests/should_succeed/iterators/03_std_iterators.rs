extern crate creusot_contracts;
use creusot_contracts::{logic::Int, std::iter::*, *};

#[requires(slice@.len() < 1000)]
#[ensures(result@ == slice@.len())]
pub fn slice_iter<T>(slice: &[T]) -> usize {
    let mut i = 0;
    #[invariant(dummy, i@ == produced.len())]
    for _ in slice.iter() {
        i += 1;
    }
    i
}

#[requires(vec@.len() < 1000)]
#[ensures(result@ == vec@.len())]
pub fn vec_iter<T>(vec: &Vec<T>) -> usize {
    let mut i = 0;
    #[invariant(dummy, i@ == produced.len())]
    for _ in vec {
        i += 1;
    }
    i
}

#[ensures(((^v)@).len() == v@.len())]
#[ensures(forall<i : _> 0 <= i && i < v@.len() ==> @((^v)@)[i] == 0)]
pub fn all_zero(v: &mut Vec<usize>) {
    #[invariant(user, forall<i : Int> 0 <= i && i < produced.len() ==> @^produced[i] == 0)]
    for x in v.iter_mut() {
        *x = 0;
    }
}

pub fn skip_take<I: Iterator>(iter: I, n: usize) {
    let res = iter.take(n).skip(n).next();

    proof_assert! { res == None };
}

pub fn counter(v: Vec<u32>) {
    let mut cnt = 0;

    let x: Vec<u32> = v
        .iter()
        .map_inv(
            #[requires(cnt@ == (*_prod).len() && cnt < usize::MAX)]
            #[ensures(cnt@ == @old(cnt) + 1 && cnt@ == (*_prod).len() + 1 && result == *x)]
            |x, _prod| {
                cnt += 1;
                *x
            },
        )
        .collect();

    proof_assert! { x@.len() == v@.len() };
    proof_assert! { x@.ext_eq(v@) };
    proof_assert! { cnt@ == x@.len() };
}

#[requires(n@ >= 0)]
#[ensures(result == n)]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    #[invariant(user, i@ == produced.len() && i <= n)]
    for _ in 0..n {
        i += 1;
    }
    i
}

pub fn enumerate_range() {
    #[invariant(id, forall<i : _> 0 <= i && i < produced.len() ==> produced[i].0 == produced[i].1 )]
    for (ix, x) in (0..10).enumerate() {
        let _ = (ix, x);
    }
}
