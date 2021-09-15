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

logic! {
    fn arith(n: Int, b: bool) -> Int {
        if !b {
            -n + n - n * n / n
        } else {
            n
        }
    }
}

logic! {
    fn deref_pat<'a>(p: &'a (Int, Int)) -> Int {
        let (a, b) = p;
        *a + *b
    }
}

#[ensures(logical())]
fn main() {}
