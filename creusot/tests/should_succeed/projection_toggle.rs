#![feature(register_tool)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

// In application the @pre should never be used
// #[ensures(toggle == true ->  (result@now == a@pre@now && result@fin == a@pre@fin && b@pre@fin == b@pre@now ))]
// #[ensures(toggle == false ->  (result@now == b@pre@now && result@fin == b@pre@fin && a@pre@fin ==  a@pre@now ))]
#[ensures(toggle == true  -> (result == a && ^ b == * b))]
#[ensures(toggle == false -> (result == b && ^ a == * a))]
fn proj_toggle<'a, T>(toggle: bool, a: &'a mut T, b: &'a mut T) -> &'a mut T {
	if toggle {
		a
	} else {
		b
	}
}

fn main () {
  let mut a = 10;
  let mut b = 5;

  let x = proj_toggle(true, &mut a, &mut b);

  *x += 5;
}
