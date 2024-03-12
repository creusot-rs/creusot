extern crate creusot_contracts;

// Check that module paths are properly printed in MLCFG.

mod a {
    pub struct T(pub u32);
}

pub struct S(pub a::T);

mod b {
    pub struct O(pub u32);

    pub mod c {
        pub struct T(pub ::a::T);

        #[allow(dead_code)]
        pub struct U(super::O);
    }
}

pub fn test(_a: a::T, _b: S, _c: b::O, _d: b::c::T) {}
