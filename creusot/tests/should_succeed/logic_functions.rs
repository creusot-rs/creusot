// SHOULD_SUCCEED: parse-print
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

mod nested {
    use creusot_contracts::*;
    logic! {
        fn logical() -> bool { true }
    }
}

logic! {
    fn logical() -> bool { false }
}

#[ensures(logical())]
fn main() {}
