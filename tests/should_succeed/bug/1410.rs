extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[warn(let_underscore_drop)]
#[requires(f.precondition(()))]
pub fn bar<F: FnMut()>(mut f: F) {
    #[invariant(inv(f))]
    #[invariant(produced.len() == 0 ==> f.precondition(()))]
    for _ in 0..1 {
        f();
    }
}
