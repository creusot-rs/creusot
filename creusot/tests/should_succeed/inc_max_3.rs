#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(*ma <= 1000_000u32 && *mb <= 1000_000u32 && *mc <= 1000_000u32)]
#[ensures(^ma != ^mb && ^mb != ^mc && ^mc != ^ma)]
fn inc_max_3<'a>(ma: &'a mut u32, mb: &'a mut u32, mc: &'a mut u32) {
  if *ma < *mb {
    let tmp = ma;
    ma = mb;
    mb = ma;
  }
  if *mb < *mc {
    let tmp = mb;
    mb = mc;
    mc = mb;
  }
  if *ma < *mb {
    let tmp = ma;
    ma = mb;
    mb = ma;
  }
  *ma += 2;
  *mb += 1;
}

#[requires(a <= 1000_000u32 && b <= 1000_000u32 && c <= 1000_000u32)]
fn test_inc_max_3(mut a: u32, mut b: u32, mut c: u32) {
  inc_max_3(&mut a, &mut b, &mut c);
  assert!(a != b && b != c && c != a);
}
