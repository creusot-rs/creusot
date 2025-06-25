// TACTIC +inline_goal
extern crate creusot_contracts;
use creusot_contracts::{logic::Int, std::iter::*, *};

#[requires(slice@.len() < 1000)]
#[ensures(result@ == slice@.len())]
pub fn slice_iter<T>(slice: &[T]) -> usize {
    let mut i = 0;
    #[invariant(i@ == produced.len())]
    for _ in slice.iter() {
        i += 1;
    }
    i
}

#[requires(vec@.len() < 1000)]
#[ensures(result@ == vec@.len())]
pub fn vec_iter<T>(vec: &Vec<T>) -> usize {
    let mut i = 0;
    #[invariant(i@ == produced.len())]
    for _ in vec {
        i += 1;
    }
    i
}

#[ensures((^v)@.len() == v@.len())]
#[ensures(forall<i> 0 <= i && i < v@.len() ==> (^v)[i]@ == 0)]
pub fn all_zero(v: &mut Vec<usize>) {
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> (^produced[i])@ == 0)]
    for x in v.iter_mut() {
        *x = 0;
    }
}

pub fn skip_take<I: Iterator>(iter: I, n: usize) {
    let res = iter.take(n).skip(n).next();

    proof_assert! { res == None };
}

pub fn counter(v: Vec<u32>) {
    let mut cnt: usize = 0;

    let x: Vec<u32> = v
        .iter()
        .map_inv(|x, _prod| {
            proof_assert!(cnt@ == _prod.len());
            cnt += 1;
            *x
        })
        .collect();

    proof_assert! { x@.len() == v@.len() };
    proof_assert! { x@.ext_eq(v@) };
    proof_assert! { cnt@ == x@.len() };
}

#[requires(n@ >= 0)]
#[ensures(result == n)]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    #[invariant(i@ == produced.len() && i <= n)]
    for _ in 0..n {
        i += 1;
    }
    i
}

pub fn enumerate_range() {
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> produced[i].0 == produced[i].1 )]
    for (ix, x) in (0..10).enumerate() {
        let _ = (ix, x);
    }
}

#[predicate]
fn equiv_range<T>(s1: Seq<T>, s2: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i> l <= i && i < u ==> s1[i] == s2[i]
    }
}

#[predicate]
fn equiv_reverse_range<T>(s1: Seq<T>, s2: Seq<T>, l: Int, u: Int, n: Int) -> bool {
    pearlite! {
        forall<i> l <= i && i < u ==> s1[i] == s2[n-i]
    }
}

#[ensures((^slice)@.ext_eq(slice@.reverse()))]
pub fn my_reverse<T>(slice: &mut [T]) {
    let n = slice.len();
    let old_v: Snapshot<Seq<T>> = snapshot! { slice@ };
    #[invariant(n@ == slice@.len())]
    #[invariant(equiv_range(slice@, *old_v, produced.len(), n@-produced.len()))]
    #[invariant(equiv_reverse_range(slice@, *old_v, 0, produced.len(), n@-1))]
    #[invariant(equiv_reverse_range(slice@, *old_v, n@-produced.len(), n@, n@-1))]
    for (i, j) in (0..n / 2).zip(0..n / 2) {
        slice.swap(i, n - j - 1);
        proof_assert!(i == j);
        proof_assert!(slice@[i@] == old_v[n@ - j@ - 1]);
        proof_assert!(slice@[n@ - j@ - 1] == old_v[i@]);
    }
}
