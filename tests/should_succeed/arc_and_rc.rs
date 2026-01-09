extern crate creusot_std;

use ::std::{rc::Rc, sync::Arc};
use creusot_std::prelude::*;

pub fn rc() {
    let rc = Rc::new(1);
    proof_assert!(*rc@ == 1i32);
    let inner = rc.as_ref();
    proof_assert!(inner@ == 1);
}

pub fn arc() {
    let arc = Arc::new(2);
    proof_assert!(*arc@ == 2i32);
    let inner = arc.as_ref();
    proof_assert!(inner@ == 2);
}
