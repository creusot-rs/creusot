extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub trait MkRef {
    #[open]
    #[logic]
    fn mk_ref(&self) -> &Self {
        self
    }
}

impl<T> MkRef for T {}

#[after_expiry('a, x.mk_ref() == (y, ()).mk_ref())]
pub fn project_deref_bad<'a>(x: (&u32, ()), y: &'a u32) -> &'a u32 {
    y
}
