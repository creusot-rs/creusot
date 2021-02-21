#![feature(register_tool, proc_macro_hygiene, stmt_expr_attributes)]
#![register_tool(creusot)]
extern crate creusot_contracts;
use creusot_contracts::*;


#[ensures(result == 10u32)]
fn unused_in_loop (b : bool) -> u32 {
    let x = 10;
    #[invariant(x, true)]
    loop {
      if b { break;}
    };
    x
}

fn main () {}
