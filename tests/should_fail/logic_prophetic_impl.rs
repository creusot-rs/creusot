extern crate creusot_std;
use creusot_std::prelude::*;

pub trait T {
    #[logic]
    fn f();
}

impl T for () {
    #[logic(open(self), prophetic)]
    fn f() {
        ()
    }
}
