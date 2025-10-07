extern crate creusot_contracts;
use creusot_contracts::*;

pub struct S1 {
    pub f: i32,
}

pub struct S2 {
    pub s1: S1,
}

pub fn test_program(s: S2) {
    s.s1.f;
}

pub fn test_assign(mut s: S2) {
    s.s1.f = 2;
}

#[allow(unused_must_use)]
#[logic(open)]
pub fn test_logic(s: S2) {
    s.s1.f;
}
