#![feature(register_tool)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

enum Option<T> { Some(T), None}

use Option::*;

fn main () {
  let mut a = Some(10);

  let b = &mut a;

  // * b = 5;


  while let Some(_) = b {
    invariant!(dummy, true);
  	*b = None;
  }

  // a == 15;
}
