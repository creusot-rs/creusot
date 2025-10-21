extern crate creusot_contracts;

mod mod1 {
    #[allow(dead_code)]
    pub enum T {
        A,
        B,
        C,
    }
}

mod mod2 {
    use crate::mod1;

    pub fn x(_t: mod1::T) -> bool {
        true
    }
}

use mod1::T::*;

pub fn f() {
    mod2::x(B);
}
