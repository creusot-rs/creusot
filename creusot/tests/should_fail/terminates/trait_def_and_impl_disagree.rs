#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

trait Tr {
    #[terminates]
    fn f();

    #[pure]
    fn g();

    #[pure]
    fn h();
}

impl Tr for i32 {
    fn f() {}

    #[terminates]
    fn g() {}

    fn h() {}
}
