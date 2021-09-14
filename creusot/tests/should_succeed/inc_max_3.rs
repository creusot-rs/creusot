#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;
use std::mem::swap;

fn inc_max_3<'a>(ma: &'a mut u32, mb: &'a mut u32, mc: &'a mut u32) {
  if *ma < *mb {
    swap(&mut ma, &mut mb);
  }
  if *mb < *mc {
    swap(&mut mb, &mut mc);
  }
  if *ma < *mb {
    swap(&mut ma, &mut mb);
  }
  *ma += 2;
  *mb += 1;
}

#[ensures(true)]
fn test_inc_max_3(mut a: u32, mut b: u32, mut c: u32) {
  inc_max_3(&mut a, &mut b, &mut c);
  assert!(a != b && b != c && c != a);
}
