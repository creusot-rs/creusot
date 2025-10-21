extern crate creusot_contracts;
use creusot_contracts::prelude::*;

enum Bad<'a> {
    None,
    Some(Snapshot<&'a mut Bad<'a>>),
}

pub fn test_bad() {
    let mut x = Bad::None;
    let m = &mut x;
    let g = snapshot!(m);
    *m = Bad::Some(g);
    proof_assert!(*m == Bad::Some(g));
    proof_assert!(^g == ^m);
    let _ = m;
    proof_assert!(^g == Bad::Some(g));
}
