extern crate creusot_contracts;
use creusot_contracts::*;

fn ex() {
    if let Some(b) = Some(true) {
        proof_assert!(b);
    }
}
