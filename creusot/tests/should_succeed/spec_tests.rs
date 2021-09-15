#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

enum T {
    A,
    B,
}

struct S<A, B>(A, B);

enum List<A> {
    Cons(A, Box<List<A>>),
    Nil,
}
use List::*;
#[ensures(equal(T::A, T::B))]
#[ensures(equal(S(0u32, true), S(1u32, false)))]
fn test_specs() {}

fn main() {}
