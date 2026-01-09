extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(false)]
pub fn main() {
    ghost! {
        let x = [0usize; usize::MAX];
        let _ = std::mem::size_of_val(&x);
    };
}
