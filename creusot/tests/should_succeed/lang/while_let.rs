extern crate creusot_contracts;
use creusot_contracts::*;

pub fn f() {
    let mut a = Some(10);
    let b = &mut a;

    #[invariant(true)]
    while let Some(_) = b {
        *b = None;
    }
}
