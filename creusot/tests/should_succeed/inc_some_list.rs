#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

/* considered to be random */
fn random() -> bool {
    true
}

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

#[requires(sum(*l) <= 2_000_000)]
#[ensures(Int::from(result) == sum(*l))]
fn sumx(l: &List) -> u32 {
    match l {
        Cons(a, l2) => *a + sumx(l2),
        Nil => 0,
    }
}

#[ensures(sum(*ml) - sum(^ml) == Int::from(*result) - Int::from(^result))]
#[ensures(Int::from(*result) <= sum(*ml))]
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

#[requires(sum(l) <= 1_000_000 && k <=1_000_000u32)]
fn inc_some_list(mut l: List, k: u32) {
    let sum0 = sumx(&l);
    let ma = take_some_list(&mut l);
    *ma += k;
    assert!(sumx(&l) == sum0 + k);
}
