extern crate creusot_contracts;
use creusot_contracts::{ghost::PtrOwn, *};

#[ensures(false)]
pub fn main() {
    ghost! {
        let x = [0usize; usize::MAX];
        let _ = ::std::mem::size_of_val(&x);
    };
}

#[ensures(false)]
pub fn g() {
    let x = [0usize; usize::MAX];
    let _ = PtrOwn::new(x);
}
