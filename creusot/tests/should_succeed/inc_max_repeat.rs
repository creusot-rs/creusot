#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

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
fn inc_max_repeat(mut a: i32, mut b: i32, n: i32) {
  let mut i: i32 = 0;
  #[invariant(cntr_bound, i < n)]
  #[invariant(diff_bound, (a - b).abs() >= i)]
  while i < n {
    let mc = take_max(&mut a, &mut b);
    *mc += 1;
    i += 1;
  }
  assert!((a - b).abs() >= i);
}
