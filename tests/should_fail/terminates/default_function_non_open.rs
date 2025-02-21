extern crate creusot_contracts;
use creusot_contracts::*;

mod inner {
    use super::*;
    pub(super) trait Foo {
        #[open(self)]
        #[logic]
        fn f() {}
        #[logic]
        fn g();
    }
}

impl inner::Foo for i32 {
    #[open(self)]
    #[logic]
    fn g() {
        Self::f(); // this assumes f could call g
    }
}
