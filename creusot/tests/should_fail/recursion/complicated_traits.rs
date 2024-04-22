#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::*;

trait Foo {
    fn foo() {}
}

impl Foo for i32 {
    fn foo() {
        bar::<std::iter::Once<i32>>(std::iter::once(1i32));
    }
}

fn bar<I>(i: I)
where
    I: Iterator,
    I::Item: Foo,
{
    for _ in i {
        I::Item::foo();
    }
}
