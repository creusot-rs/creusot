extern crate creusot_contracts;
use creusot_contracts::*;

pub trait Foo {
    #[check(terminates)]
    fn f() {}
    #[check(terminates)]
    fn g();
}

impl Foo for i32 {
    #[check(terminates)]
    fn g() {
        Self::f(); // this assumes f could call g
    }
}
