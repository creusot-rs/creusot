extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let mut a = Some(10);
    let b = &mut a;

    #[invariant(true)]
    while let Some(_) = b {
        *b = None;
    }
}
