extern crate creusot_contracts;
use creusot_contracts::*;

enum Bad<'a> {
    None,
    Some(Ghost<&'a mut Bad<'a>>),
}

pub fn test_bad() {
    let mut x = Bad::None;
    let m = &mut x;
    let g = gh!(m);
    *m = Bad::Some(g);
    proof_assert!(*m == Bad::Some(g));
    proof_assert!(^*g == ^m);
    let _ = m;
    proof_assert!(^*g == Bad::Some(g));
}
