extern crate creusot_contracts;
use creusot_contracts::{ghost::PtrOwn, prelude::*};

pub struct S {
    pub perm: Ghost<PtrOwn<i32>>,
    pub ptr: *const i32,
}

impl S {
    #[requires(self.perm.val()@ == 1)]
    #[requires(self.perm.tied() == self.ptr)]
    pub fn minimize(&mut self) {
        let r = unsafe { PtrOwn::as_ref(self.ptr, ghost!(&*self.perm)) };
        #[invariant(0 <= self.perm.val()@)]
        loop {
            let _ = *r;
        }
    }
}
