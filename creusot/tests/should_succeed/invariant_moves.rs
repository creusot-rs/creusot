#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

fn test_invariant_move(mut x: Vec<u32>) {
    #[invariant(dummy, equal(x, x))]
    while let Some(x) = { (&mut x).pop() } {}
}
