extern crate creusot_std;
use creusot_std::prelude::*;

pub fn g() {
    ghost! {
        fn _f() {
            ghost! {
               proof_assert!{mode!().ghost()}
            };
            proof_assert!(!mode!().ghost());
        }
    };
}
