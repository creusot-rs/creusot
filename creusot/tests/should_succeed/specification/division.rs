#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

#[requires(x != 0u32)]
fn divide(y: u32, x: u32) -> u32 {
    y / x
}
