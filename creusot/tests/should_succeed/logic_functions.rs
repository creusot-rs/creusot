// SHOULD_SUCCEED: parse-print
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
fn logic() -> bool {
    true
}

#[ensures(logic())]
fn use_logic() {}

// To use pearlite syntax like `===`,
// we need to use `logic_fn!` instead of `#[logic]`
logic_fn! {
    fn logical() -> bool {
        0 === 0
    }
}

#[ensures(logical())]
fn use_logical() {}

mod nested {
    use creusot_contracts::*;

    #[logic]
    fn nested() -> bool {
        true
    }
}

#[logic]
fn arith(n: Int, b: bool) -> Int {
    if !b {
        -n + n - n * n
    } else {
        n
    }
}

#[logic]
fn deref_pat<'a>(o: &'a Option<Int>) -> Int {
    match o {
        Some(a) => *a,
        None => Int::from(0),
    }
}
