// WHY3PROVE
extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(*(result.0) == *x)]
pub fn reborrow_tuple<T>(x: &mut T) -> (&mut T, u32) {
    (x, 32)
}

#[ensures(false)]
pub fn test() {
    let mut x = 5;
    let (res, _) = reborrow_tuple(&mut x);
    proof_assert!(^res == 5i32);
    *res = 10;
}
