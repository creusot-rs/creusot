extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S1 {
    pub f: i32,
}

pub struct S2 {
    pub s1: S1,
}

pub fn test_program(s: S2) {
    s.s1.f;
}

#[allow(unused)]
pub fn test_assign(mut s: S2) -> S2 {
    s.s1.f = 2;
    s
}

#[allow(unused_must_use)]
#[logic(open)]
pub fn test_logic(s: S2) {
    s.s1.f;
}
