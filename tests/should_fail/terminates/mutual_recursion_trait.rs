#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::prelude::*;

trait Foo {
    #[check(terminates)]
    fn foo() {}
}

impl Foo for i32 {
    #[check(terminates)]
    fn foo() {
        bar();
    }
}

#[check(terminates)]
fn bar() {
    <i32 as Foo>::foo();
}
