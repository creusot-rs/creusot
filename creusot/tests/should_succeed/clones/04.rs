// SHOULD_SUCCEED: parse-print
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

#[logic_rust]
fn a(x: u32) -> bool {
    x > 0u32
}

#[logic_rust]
fn b(x: u32) -> bool {
    x > 10u32 && a(x)
}

#[logic_rust]
fn c(x: u32) -> bool {
    x < 50u32 && b(x)
}

#[requires(c(x))]
fn f(x: u32) {}
