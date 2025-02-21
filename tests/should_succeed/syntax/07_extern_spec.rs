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

impl UseSelf for i32 {
    #[trusted]
    fn func(&self, _: &i32) -> bool {
        *self == 1
    }
}

extern_spec! {
    impl UseSelf for () {
        fn func(&self, s: &Self) -> bool;
    }

    impl UseSelf for i32 {
        #[ensures(result == (*self == 1i32))]
        fn func(&self, s: &Self) -> bool {
            *self == 1
        }
    }
}

use std::ops::Add;
// Checks that we can properly translate extern specs that refer to late bound parameters
extern_spec! {
    impl<'a> Add<&'a u16> for u16 {
        fn add(self, a: & u16) -> u16;
    }
}
