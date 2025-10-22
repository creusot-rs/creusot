#![feature(min_specialization)]
extern crate creusot_contracts;
use creusot_contracts::{prelude::*, resolve::structural_resolve};

pub struct False;

impl Resolve for False {
    #[logic(open, prophetic)]
    #[ensures(structural_resolve(self) ==> result)]
    fn resolve(self) -> bool {
        false
    }
}

pub struct P<T>(T);

impl<T> Resolve for P<T> {
    #[logic(open, prophetic)]
    #[ensures(structural_resolve(self) ==> result)]
    fn resolve(self) -> bool {
        false
    }
}
