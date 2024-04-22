#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

trait Foo {
    fn foo() {}
}

impl Foo for i32 {
    fn foo() {
        bar();
    }
}

fn bar() {
    <i32 as Foo>::foo();
}
