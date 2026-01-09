extern crate creusot_std;
use creusot_std::prelude::*;

pub fn ex() {
    if let Some(b) = Some(true) {
        proof_assert!(b);
    }
}
