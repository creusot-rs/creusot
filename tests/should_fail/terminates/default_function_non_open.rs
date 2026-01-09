extern crate creusot_std;
use creusot_std::prelude::*;

pub mod inner {
    use super::*;
    pub trait Foo {
        #[logic(open(self))]
        fn f() {}
        #[logic]
        fn g();
    }
}

impl inner::Foo for i32 {
    #[logic(open(self))]
    fn g() {
        Self::f(); // this assumes f could call g
    }
}
