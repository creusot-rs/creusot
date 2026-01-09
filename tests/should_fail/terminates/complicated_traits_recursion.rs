#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

trait Foo {
    #[check(terminates)]
    fn foo() {}
}

impl Foo for i32 {
    #[check(terminates)]
    fn foo() {
        bar::<std::iter::Once<i32>>(std::iter::once(1i32));
    }
}

#[check(terminates)]
fn bar<I>(_: I)
where
    I: Iterator,
    I::Item: Foo,
{
    I::Item::foo()
}
