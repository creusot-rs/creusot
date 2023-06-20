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

#[ensures({let x = old(x.mk_ref()); match x {None => true, Some(_) => true}})]
pub fn bad_ref_match(x: Option<Box<u32>>) {}
