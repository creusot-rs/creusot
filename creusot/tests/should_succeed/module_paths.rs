// SHOULD_SUCCEED: parse-print
// Check that module paths are properly printed in MLCFG.

mod a {
    pub struct T(u32);
}

pub struct S(a::T);

mod b {
    pub struct O(u32);

    pub mod c {
        pub struct T(::a::T);
        // FIXME: Currently cannot handle types that depend on outer modules!
        // pub struct U(super::O);
    }
}

fn test(a: a::T, b: S, c: b::O, d: b::c::T) {}

fn main() {}
