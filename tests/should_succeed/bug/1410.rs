extern crate creusot_std;
use creusot_std::prelude::*;

#[warn(let_underscore_drop)]
#[requires(|mode| f.precondition(mode, ()))]
pub fn bar<F: FnMut()>(mut f: F) {
    #[invariant(|mode| produced.len() == 0 ==> f.precondition(mode, ()))]
    for _ in 0..1 {
        f();
    }
}
