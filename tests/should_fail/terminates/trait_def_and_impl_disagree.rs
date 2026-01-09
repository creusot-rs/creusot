#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

trait Tr {
    #[check(terminates)]
    fn f();

    #[check(ghost)]
    fn g();

    #[check(ghost)]
    fn h();
}

impl Tr for i32 {
    fn f() {}

    #[check(terminates)]
    fn g() {}

    fn h() {}
}
