#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

logic! {
    fn id<T>(x : T) -> T { x }
}

trait A {
    type T;

    #[ensures(equal(id(x), x))]
    fn f(x: Self::T);
}

fn test<T: A>(_: T) {}
