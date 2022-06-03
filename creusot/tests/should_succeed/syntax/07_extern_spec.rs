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

use std::ops::Add;
// Checks that we can properly translate extern specs that refer to late bound parameters
extern_spec! {
    impl<'a> Add<&'a u16> for u16 {
        fn add(self, a: & u16) -> u16;
    }
}
