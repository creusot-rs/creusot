extern crate creusot_contracts;
use creusot_contracts::ghost_ptr::GhostPtrToken;
pub fn test() {
    let mut token = GhostPtrToken::new();
    let ptr1 = token.ptr_from_box(Box::new(1));
    let ptr2 = token.ptr_from_box(Box::new(2));

    let mut token_mut = token.borrow_mut();
    let m1 = token_mut.take_mut(ptr1);
    let m2 = token_mut.take_mut(ptr2);

    assert_eq!(*m1, 1);
    assert_eq!(*m2, 2);

    core::mem::swap(m1, m2);
    assert_eq!(*token.ptr_as_ref(ptr1), 2);
    assert_eq!(*token.ptr_as_ref(ptr2), 1);
}
