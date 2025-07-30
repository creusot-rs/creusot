#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

trait Foo {
    #[safety(terminates)]
    fn foo() {}
}

impl Foo for i32 {
    #[safety(terminates)]
    fn foo() {
        bar();
    }
}

#[safety(terminates)]
fn bar() {
    <i32 as Foo>::foo();
}
