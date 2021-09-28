#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

logic! {
    fn reflexive<T : PartialEq>(x : T) -> bool {
        true == true
    }
}

#[ensures(reflexive(result))]
fn dummy() -> u32 {
    0
}
