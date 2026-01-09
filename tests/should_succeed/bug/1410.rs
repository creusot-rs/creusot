extern crate creusot_std;
use creusot_std::prelude::*;

#[warn(let_underscore_drop)]
#[requires(f.precondition(()))]
pub fn bar<F: FnMut()>(mut f: F) {
    #[invariant(produced.len() == 0 ==> f.precondition(()))]
    for _ in 0..1 {
        f();
    }
}
