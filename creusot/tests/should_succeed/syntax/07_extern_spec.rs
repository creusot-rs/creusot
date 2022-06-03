#![allow(unused_variables)]

extern crate creusot_contracts;
use creusot_contracts::*;

trait UseSelf {
    fn func(&self, rhs: &Self) -> bool;
}

impl UseSelf for () {
    fn func(&self, _: &()) -> bool {
        true
    }
}

extern_spec! {
    impl UseSelf for () {
        fn func(&self,  s: &Self) -> bool;
    }
}
