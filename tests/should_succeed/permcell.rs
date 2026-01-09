extern crate creusot_std;
use creusot_std::{cell::PermCell, prelude::*};

#[ensures(result@ == 3)]
pub fn foo() -> i32 {
    let (p, mut own) = PermCell::new(1i32);

    assert!(unsafe { *p.borrow(ghost!(&**own)) } == 1);

    unsafe {
        *p.borrow_mut(ghost!(&mut **own)) = 2;
    }
    assert!(unsafe { *p.borrow(ghost!(&**own)) } == 2);

    assert!(unsafe { p.replace(ghost!(&mut **own), 3) } == 2);
    p.into_inner(own)
}
