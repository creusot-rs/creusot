#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

trait Foo {
    #[terminates]
    fn foo() {}
}

impl Foo for i32 {
    #[terminates]
    fn foo() {
        bar();
    }
}

#[terminates]
fn bar() {
    <i32 as Foo>::foo();
}
