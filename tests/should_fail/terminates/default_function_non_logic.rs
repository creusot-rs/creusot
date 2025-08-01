extern crate creusot_contracts;
use creusot_contracts::*;

pub trait Foo {
    #[safety(terminates)]
    fn f() {}
    #[safety(terminates)]
    fn g();
}

impl Foo for i32 {
    #[safety(terminates)]
    fn g() {
        Self::f(); // this assumes f could call g
    }
}
