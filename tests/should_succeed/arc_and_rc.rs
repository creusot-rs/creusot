extern crate creusot_std;

use ::std::{rc::Rc, sync::Arc};
use creusot_std::prelude::*;

pub fn rc() {
    let rc = Rc::new(1);
    proof_assert!(*rc@ == 1i32);
    let inner = rc.as_ref();
    proof_assert!(inner@ == 1);

    let rc2 = rc.clone();
    proof_assert!(rc == rc2);

    let b = Rc::ptr_eq(&rc, &rc2);
    proof_assert!(b);

    let rc3 = Rc::new(2);
    let b2 = Rc::ptr_eq(&rc, &rc3);
    // the content of the two rc is not the same, so their pointer have to be different
    proof_assert!(!b2);
}

pub fn arc() {
    let arc = Arc::new(1);
    proof_assert!(*arc@ == 1i32);
    let inner = arc.as_ref();
    proof_assert!(inner@ == 1);

    let arc2 = arc.clone();
    proof_assert!(arc == arc2);

    let b = Arc::ptr_eq(&arc, &arc2);
    proof_assert!(b);

    let arc3 = Arc::new(2);
    let b2 = Arc::ptr_eq(&arc, &arc3);
    // the content of the two arc is not the same, so their pointer have to be different
    proof_assert!(!b2);
}
