// WHY3PROVE
extern crate creusot_std;
use creusot_std::{invariant::Invariant, prelude::*};

#[allow(dead_code)]
struct S<T>(i32, *const T);

impl Invariant for S<i32> {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! { self.0@ == 0 }
    }
}

#[ensures(result.0 == t)]
fn mk_s<T>(t: i32) -> S<T> {
    return S::<T>(t, std::ptr::null());
}

pub fn evil() {
    let _s = mk_s::<i32>(1);
    proof_assert!(false)
}
