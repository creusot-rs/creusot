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

/* TODO: prove this lemma */
#[trusted]
#[ensures(sum_list(*l) >= 0)]
fn lemma_sum_list_nonneg(l: &List) {}

#[requires(sum_list(*l) <= 1_000_000)]
#[ensures(Int::from(result) == sum_list(*l))]
fn sum_list_x(l: &List) -> u32 {
  match l {
    Cons(a, l2) => *a + sum_list_x(l2),
    Nil => 0,
  }
}

#[ensures(sum_list(*ml) - sum_list(^ml) == Int::from(*result) - Int::from(^result))]
#[ensures(Int::from(*result) <= sum_list(*ml))]
fn take_some_list(ml: &mut List) -> &mut u32 {
  match ml {
    Cons(ma, ml2) => {
      lemma_sum_list_nonneg(ml2);
      if rand::random() {
        ma
      } else {
        take_some_list(ml2)
      }
    }
    Nil => loop {},
  }
}

#[requires(sum_list(l) + Int::from(k) <= 1_000_000)]
fn inc_some_list(mut l: List, k: u32) {
  let sum0 = sum_list_x(&l);
  let ma = take_some_list(&mut l);
  *ma += k;
  assert!(sum_list_x(&l) == sum0 + k);
}
