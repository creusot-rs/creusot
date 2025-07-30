#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

trait Tr {
    #[safety(terminates)]
    fn f();

    #[safety(ghost)]
    fn g();

    #[safety(ghost)]
    fn h();
}

impl Tr for i32 {
    fn f() {}

    #[safety(terminates)]
    fn g() {}

    fn h() {}
}
