extern crate creusot_std;
use creusot_std::prelude::*;

pub fn foo() {
    let mut mapping = snapshot!(|_| 42);

    mapping = snapshot!(mapping.set(0, 10));
    proof_assert!(mapping[0] == 10);
    proof_assert!(mapping[1] == 42);
    mapping = snapshot!(mapping.set(1, 11));
    proof_assert!(mapping[0] == 10);
    proof_assert!(mapping[1] == 11);
    mapping = snapshot!(mapping.set(0, 12));
    proof_assert!(mapping[0] == 12);
    proof_assert!(mapping[1] == 11);
}
