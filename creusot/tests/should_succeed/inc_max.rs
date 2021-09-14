#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

fn take_max<'a>(ma: &'a mut u32, mb: &'a mut u32) -> &'a mut u32 {
  if *ma >= *mb {
    ma
  } else {
    mb
  }
}

#[ensures(true)]
fn inc_max(mut a: u32, mut b: u32) {
  let mc = take_max(&mut a, &mut b);
  *mc += 1;
  assert!(a != b);
}
