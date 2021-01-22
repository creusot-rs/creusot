#![feature(register_tool)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(toggle == true -> result == a)]
#[ensures(toggle == false -> result == b)]
fn proj_toggle<'a, T>(toggle: bool, a: &'a mut T, b: &'a mut T) -> &'a mut T {
	if toggle {
		a
	} else {
		b
	}
}

fn main () {}
