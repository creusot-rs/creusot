#![feature(register_tool)]
#![register_tool(creusot)]
extern crate creusot_contracts;
use creusot_contracts::*;


#[ensures(result == 10)]
fn unused_in_loop (b : bool) -> u32 {
    let x = 10;
    invariant!(x, true);
    loop {
      if b { break;}
    };
    x
}

fn main () {}
