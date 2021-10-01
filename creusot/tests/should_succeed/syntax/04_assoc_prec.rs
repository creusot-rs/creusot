#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

// TODO: these could be unit tests in the why3 crate

#[ensures(5 == 3 ==> 2 + 1 == 3)]
#[ensures(5 * 3 / 2 != 4 * (40 + 1))]
#[ensures((x.0) == (x.1))] // TODO: Fix syn parser.
fn respect_prec(x: (u32, u32)) {}

#[ensures(Int::from(0u32) + Int::from(1u32) == 0)]
fn respect_assoc() {}
