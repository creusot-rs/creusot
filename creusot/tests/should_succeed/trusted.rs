// SHOULD_SUCCEED: parse-print
#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

#[trusted]
fn external() {
  println!("Hello world!");
}

#[trusted]
#[ensures(result == 10u32)]
fn lie() -> u32 {
  5 // I'm evil
}

#[ensures(result == 10u32)]
fn victim_of_lie() -> u32 {
  lie()
}

predicate! {
  #[trusted]
  fn trusted_pred(x: u32) {
    true
  }
}
