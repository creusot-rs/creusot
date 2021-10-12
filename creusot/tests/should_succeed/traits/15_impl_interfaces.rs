#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

// Verifies that instances are properly cloned as interfaces in
// the interfaces of functions. Also ensures that we don't attempt
// refine associated types of instances.

trait Tr {
    type A;
}

impl Tr for () {
    type A = ();
}

#[trusted]
#[logic_rust]
fn x<T: Tr>(x: T) -> T::A {
    panic!()
}

#[requires(x(a) === ())]
fn calls(a: ()) -> <() as Tr>::A {}

// This call used to break
#[ensures(x(a) === ())]
fn breaks(a: ()) {
    calls(a)
}
