// SHOULD_SUCCEED: parse-print
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

#[logic_rust]
fn omg<T>(x: T) -> bool {
    true
}

#[ensures(omg(x))]
fn prog<T>(x: T) {}

#[ensures(omg(0))]
fn prog2() {
    prog(0);
}

#[ensures(omg((0, 0)))]
fn prog3() {}
