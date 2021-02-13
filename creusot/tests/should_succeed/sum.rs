#![feature(register_tool)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result == n * (n + 1) / 2)]
fn sum_first_n(n: u32) -> u32 {
  let mut sum = 0;
  let mut i = 0;
  #[invariant(loop_bound, i < n + 1)]
  #[invariant(sum_value, sum == i * (i + 1) / 2)]
  while i <= n {
    sum += i;
    i += 1;
  }
  sum
}

fn main () {}
