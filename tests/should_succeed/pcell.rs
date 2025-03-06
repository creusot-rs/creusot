extern crate creusot_contracts;
use creusot_contracts::{pcell::PCell, *};

#[ensures(result@ == 3)]
pub fn foo() -> i32 {
    let (p, mut own) = PCell::new(1i32);

    assert!(unsafe { *p.borrow(own.borrow()) } == 1);

    unsafe {
        *p.borrow_mut(own.borrow_mut()) = 2;
    }
    assert!(unsafe { *p.borrow(own.borrow()) } == 2);

    assert!(unsafe { p.replace(own.borrow_mut(), 3) } == 2);
    p.into_inner(own)
}
