#![feature(register_tool)]
#![register_tool(creusot)]
extern crate creusot_contracts;


pub mod nested {
  use creusot_contracts::*;

  enum Nested { Test }

	#[ensures(result == true)]
	pub fn inner_func() -> bool {
		Nested::Test;
		true
	}
	pub mod further {
		pub fn another() -> bool {
			false
		}
	}
}
fn main () {
	nested::inner_func();
	use nested::further::*;
	another();
}
