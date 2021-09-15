#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(if *ma >= *mb { equal(*mb, ^mb) && equal(result, ma) }
                   else { equal(*ma, ^ma) && equal(result, mb) })]
fn take_max<'a>(ma: &'a mut u32, mb: &'a mut u32) -> &'a mut u32 {
  if *ma >= *mb {
    ma
  } else {
    mb
  }
}

#[requires(a <= 1_000_000u32 && b <= 1_000_000u32 && n <= 1_000_000u32)]
fn inc_max_repeat(mut a: u32, mut b: u32, n: u32) {
  let mut i: u32 = 0;
  #[invariant(cntr_bound, i <= n)]
  #[invariant(val_bound, a <= 1_000_000u32 + i && b <= 1_000_000u32 + i)]
  #[invariant(diff_bound, a >= b + i || b >= a + i) ]
  while i < n {
    let mc = take_max(&mut a, &mut b);
    *mc += 1;
    i += 1;
  }
  assert!(a >= b + i || b >= a + i);
}
