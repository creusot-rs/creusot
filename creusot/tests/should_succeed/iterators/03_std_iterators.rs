extern crate creusot_contracts;
use creusot_contracts::*;

#[requires((@slice).len() < 1000)]
#[ensures(@result == (@slice).len())]
pub fn slice_iter<T>(slice: &[T]) -> usize {
    let mut i = 0;
    #[invariant(dummy, @i == produced.len())]
    for _ in slice.iter() {
        i += 1;
    }
    i
}

#[requires((@vec).len() < 1000)]
#[ensures(@result == (@vec).len())]
pub fn vec_iter<T>(vec: &Vec<T>) -> usize {
    let mut i = 0;
    #[invariant(dummy, @i == produced.len())]
    for _ in vec {
        i += 1;
    }
    i
}

#[ensures((@^v).len() == (@v).len())]
#[ensures(forall<i : _> 0 <= i && i < (@v).len() ==> @(@^v)[i] == 0)]
pub fn all_zero(v: &mut Vec<usize>) {
    #[invariant(user, forall<i : Int> 0 <= i && i < produced.len() ==> @^produced[i] == 0)]
    for x in v.iter_mut() {
        *x = 0;
    }
}
