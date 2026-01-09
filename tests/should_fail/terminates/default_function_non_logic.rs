extern crate creusot_std;
use creusot_std::prelude::*;

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
