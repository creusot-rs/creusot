#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

fn main() {}

// Fix spec parser!
// #[ensures(^ x.0 == * x.0)]
// #[ensures(^ x.1 == * x.1)]
#[ensures(x.resolve())]
fn drop_pair(x: (&mut u32, &mut u32)) {}

fn drop_pair2(x: (&mut u32, &mut u32)) {
    x;
}

// Checks that we generate drop for x which is always init but never live *and* written to.
// However we should *not* get a drop for *y*
fn drop<'a>(mut x: &'a mut u32, y: &'a mut u32) {
    x = y;
}
