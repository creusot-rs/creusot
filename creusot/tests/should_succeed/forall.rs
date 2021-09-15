#![feature(register_tool, rustc_attrs, stmt_expr_attributes)]
#![register_tool(creusot)]

extern crate creusot_contracts;

use creusot_contracts::*;

#[ensures(forall<x:u32> true && true && true && true && true && true && true && true && true)]
fn main() {}
