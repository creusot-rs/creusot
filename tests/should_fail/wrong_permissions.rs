// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::{
    cell::{PermCell, PermCellOwn},
    ghost::PtrOwn,
    *,
};

pub fn unknown_permcell_permission(cell: &PermCell<i32>, perm: Ghost<&PermCellOwn<i32>>) {
    // does not work: we don't know if cell and perm have the same id
    let _ = unsafe { cell.borrow(perm) };
}
pub fn wrong_permcell_permission() {
    let (cell, _) = PermCell::new(1i32);
    let (_, perm) = PermCell::new(1i32);

    // does not work: we know that `perm` is not `cell`'s permission
    let _ = unsafe { cell.borrow(perm.borrow()) };
}

pub fn unknown_ptr_own_permission(ptr: *const i32, perm: Ghost<&PtrOwn<i32>>) {
    // does not work: we don't know if ptr and perm have the same id
    let _ = unsafe { PtrOwn::as_ref(ptr, perm) };
}
pub fn wrong_ptr_own_permission() {
    let (ptr, _) = PtrOwn::new(1i32);
    let (_, perm) = PtrOwn::new(1i32);

    // does not work: we know that `perm` is not `ptr`'s permission
    let _ = unsafe { PtrOwn::as_ref(ptr, perm.borrow()) };
}
