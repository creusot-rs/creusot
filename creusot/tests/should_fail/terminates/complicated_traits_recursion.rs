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
        bar::<std::iter::Once<i32>>(std::iter::once(1i32));
    }
}

#[terminates]
fn bar<I>(_: I)
where
    I: Iterator,
    I::Item: Foo,
{
    I::Item::foo()
}
