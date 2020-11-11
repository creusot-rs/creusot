#![feature(register_tool)]
#![register_tool(creusot)]
extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(   x <= 100 ==> result == 91
          && x > 100 ==> result == x - 10)]
fn mc91(x: u32) -> u32 {
  if x > 100 {
    x - 10
  } else {
    mc91(mc91(x + 11))
  }
}

fn main () { }
