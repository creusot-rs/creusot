#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

logic! {
    fn unary_op(n: i32, b: bool) -> i32 {
        if !b {
            -n
        } else {
            n
        }
    }
}

logic! {
    fn deref_pat<'a>(p: &'a (i32, i32)) -> i32 {
        let (a, b) = p;
        *a + *b
    }
}
