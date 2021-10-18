// WHY3PROVE
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]
#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

#[ensures(@(@^v)[(@v).len()] === (@v).len())]
fn test(v: &mut Vec<usize>) {
    v.push(v.len());
}
