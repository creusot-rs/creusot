#![feature(register_tool)]
#![register_tool(creusot)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result == n * (n - 1) / 2)]
fn sum_first_n(n: u32) -> u32 {
  let mut sum = 0;
  let mut i = 0;
  while i <= n {
    invariant!(xx, sum == i * (i - 1) / 2);
    sum += i;
    i += 1;
  }
  sum
}

fn main () {}
