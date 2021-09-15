#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

/* considered to be random */
fn random() -> bool {
    true
}

fn clone() {}

enum List {
    Cons(u32, Box<List>),
    Nil,
}
use List::*;

logic! {
fn sum(l: List) -> Int {
    match l {
        Cons(a, l2) => Int::from(a) + sum(*l2),
        Nil => 0,
    }
}
}

#[ensures(sum(*ml) + Int::from(^result) == sum(^ml) + Int::from(*result))]
fn take_some_list(ml: &mut List) -> &mut u32 {
    match ml {
        Cons(ma, ml2) => {
            if random() {
                ma
            } else {
                take_some_list(ml2)
            }
        }
        Nil => loop {},
    }
}
