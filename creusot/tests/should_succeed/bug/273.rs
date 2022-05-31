extern crate creusot_contracts;
use creusot_contracts::*;

pub fn ex() {
    if let Some(b) = Some(true) {
        proof_assert!(b);
    }
}
