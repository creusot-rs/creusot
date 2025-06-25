extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures((^v)@.len() == v@.len())]
#[ensures(forall<i> 0 <= i && i < v@.len() ==> (^v)[i] == v[i])]
pub fn change_capacity<T>(v: &mut Vec<T>) {
    v.reserve(100);
    v.reserve_exact(200);
    v.shrink_to_fit();
    v.shrink_to(1);
}

#[ensures((^v)@.len() == 0)]
pub fn clear_vec<T>(v: &mut Vec<T>) {
    v.clear();
}
