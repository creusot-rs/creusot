extern crate creusot_std;
use creusot_std::prelude::{vec, *};

pub fn can_extend() {
    let mut v = vec![1, 2, 3];
    let w = vec![4, 5, 6];
    v.extend(w);

    let z = vec![1, 2, 3, 4, 5, 6];
    proof_assert!(z@.ext_eq(v@));
}
