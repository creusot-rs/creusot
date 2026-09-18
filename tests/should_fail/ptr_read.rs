// WHY3PROVE
extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*, std::ptr::read};

#[ensures(result == *r)]
pub unsafe fn f<T>(r: &mut T) -> T {
    unsafe {
        let (ptr, mut perm) = Perm::from_mut(r);
        read(ptr, ghost! {perm.borrow}).0
    }
}
