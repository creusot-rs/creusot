extern crate creusot_contracts;
use creusot_contracts::*;

// This tests showcases specialization of purity attribute when calling trait implementations.

trait Foo {
    fn f();
}

impl Foo for i32 {
    #[terminates]
    fn f() {}
}

#[terminates]
pub fn calls_f() {
    <i32 as Foo>::f()
}

pub trait Bar {
    #[logic(prophetic)]
    fn g() -> Int;
}

impl Bar for i32 {
    #[logic]
    #[open]
    fn g() -> Int {
        1
    }
}

#[logic]
#[open]
pub fn calls_g() -> Int {
    <i32 as Bar>::g()
}

pub fn result() {
    proof_assert!(calls_g() == 1);
}
