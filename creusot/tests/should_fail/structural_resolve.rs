#![feature(min_specialization)]
extern crate creusot_contracts;
use creusot_contracts::{resolve::structural_resolve, *};

pub struct False;

impl Resolve for False {
    #[open]
    #[predicate(prophetic)]
    #[ensures(structural_resolve(&self) ==> result)]
    fn resolve(self) -> bool {
        false
    }
}

pub struct P<T>(T);

impl<T> Resolve for P<T> {
    #[open]
    #[predicate(prophetic)]
    #[ensures(structural_resolve(&self) ==> result)]
    fn resolve(self) -> bool {
        false
    }
}
