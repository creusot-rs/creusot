// UNBOUNDED
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

#[ensures(result == 4294967294u32)]
fn no_bounds_check(x: u32, y: u32) -> u32 {
  2_147_483_647 + 2_147_483_647
}