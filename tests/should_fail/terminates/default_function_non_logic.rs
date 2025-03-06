extern crate creusot_contracts;
use creusot_contracts::*;

trait Foo {
    #[terminates]
    fn f() {}
    #[terminates]
    fn g();
}

impl Foo for i32 {
    #[terminates]
    fn g() {
        Self::f(); // this assumes f could call g
    }
}
