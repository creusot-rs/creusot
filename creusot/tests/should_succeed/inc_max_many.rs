#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

fn take_max<'a>(ma: &'a mut i32, mb: &'a mut i32) -> &'a mut i32 {
  if *ma >= *mb {
    ma
  } else {
    mb
  }
}

#[ensures(true)]
fn inc_max_many(mut a: i32, mut b: i32, k: i32) {
  let mc = take_max(&mut a, &mut b);
  *mc += k;
  assert!((a - b).abs() >= k);
}
