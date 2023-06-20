extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub trait MkRef {
    #[open]
    #[logic(('x) -> 'x)]
    fn mk_ref(&self) -> &Self {
        self
    }
}

impl<T> MkRef for T {}

#[ensures(result == *old(x.0.mk_ref()))]
pub fn project_deref_bad<'a>(x: Box<(u32, u32)>) -> u32 {
    (*x).0
}