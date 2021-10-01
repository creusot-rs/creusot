#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

enum List {
    Cons(u32, Box<List>),
    Nil,
}
use List::*;

logic! {
    fn sum_list(l: List) -> Int {
        match l {
            Cons(a, l2) => Int::from(a) + sum_list(*l2),
            Nil => 0,
        }
    }
}

// TODO: Make this ghost
#[ensures(sum_list(*l) >= 0)]
fn lemma_sum_list_nonneg(l: &List) {
    match l {
        Cons(_, l) => lemma_sum_list_nonneg(l),
        Nil => (),
    }
}

#[requires(sum_list(*l) <= 1_000_000)]
#[ensures(Int::from(result) == sum_list(*l))]
fn sum_list_x(l: &List) -> u32 {
    match l {
        Cons(a, l2) => *a + sum_list_x(l2),
        Nil => 0,
    }
}

#[ensures(sum_list(^ml) - sum_list(*ml) ==
  Int::from(^result.0) + sum_list(^result.1) - Int::from(*result.0) - sum_list(*result.1))]
#[ensures(Int::from(*result.0) <= sum_list(*ml))]
#[ensures(sum_list(*result.1) <= sum_list(*ml))]
fn take_some_rest_list(ml: &mut List) -> (&mut u32, &mut List) {
    match ml {
        Cons(ma, ml2) => {
            lemma_sum_list_nonneg(ml2);
            if rand::random() {
                (ma, ml2)
            } else {
                take_some_rest_list(ml2)
            }
        }
        Nil => loop {},
    }
}

#[requires(sum_list(l) + Int::from(j) + Int::from(k) <= 1_000_000)]
fn inc_some_2_list(mut l: List, j: u32, k: u32) {
    let sum0 = sum_list_x(&l);
    let (ma, ml) = take_some_rest_list(&mut l);
    let (mb, _) = take_some_rest_list(ml);
    *ma += j;
    *mb += k;
    assert!(sum_list_x(&l) == sum0 + j + k);
}
