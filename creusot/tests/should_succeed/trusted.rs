// SHOULD_SUCCEED: parse-print
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

#[trusted]
fn omg() {}

#[trusted]
#[ensures(result == 10u32)]
fn omg2() -> u32 {
  5 // im evil
}

