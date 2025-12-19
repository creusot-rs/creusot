// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::{cell::PermCell, ghost::perm::Perm, prelude::*};

pub fn unknown_permcell_permission(cell: &PermCell<i32>, perm: Ghost<&Perm<PermCell<i32>>>) {
    // does not work: we don't know if cell and perm have the same id
    let _ = unsafe { cell.borrow(perm) };
}
pub fn wrong_permcell_permission() {
    let (cell, _) = PermCell::new(1i32);
    let (_, perm) = PermCell::new(1i32);

    // does not work: we know that `perm` is not `cell`'s permission
    let _ = unsafe { cell.borrow(ghost!(&**perm)) };
}

pub fn unknown_ptr_perm_permission(ptr: *const i32, perm: Ghost<&Perm<*const i32>>) {
    // does not work: we don't know if ptr and perm have the same id
    let _ = unsafe { Perm::as_ref(ptr, perm) };
}
pub fn wrong_ptr_perm_permission() {
    let (ptr, _) = Perm::new(1i32);
    let (_, perm) = Perm::new(1i32);

    // does not work: we know that `perm` is not `ptr`'s permission
    let _ = unsafe { Perm::as_ref(ptr, ghost!(&**perm)) };
}
