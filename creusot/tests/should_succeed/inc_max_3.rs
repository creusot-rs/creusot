#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(equal(^mma, *mmb) && equal(^mmb, *mma))]
fn swap<'a>(mma: &'a mut &'a mut u32, mmb: &'a mut &'a mut u32) {
  let tmp = *mma;
  *mma = *mmb;
  *mmb = tmp;
}

#[requires(*ma <= 1_000_000u32 && *mb <= 1_000_000u32 && *mc <= 1_000_000u32)]
#[ensures(^ma != ^mb && ^mb != ^mc && ^mc != ^ma)]
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

#[requires(a <= 1_000_000u32 && b <= 1_000_000u32 && c <= 1_000_000u32)]
fn test_inc_max_3(mut a: u32, mut b: u32, mut c: u32) {
  inc_max_3(&mut a, &mut b, &mut c);
  assert!(a != b && b != c && c != a);
}
