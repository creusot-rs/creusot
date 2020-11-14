#![feature(register_tool)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(forall<i1 : usize, i2 : usize>
  0 <= i1 && i1 <= i2 && i2 < vec.len() -> a[i1] <= a[i2])]
#[ensures(match result {
	Ok(x) => vec[x] == v,
	Err(x) => if x < vec.len() {
			vec[x - 1] < v && v < vec[x] // insert into vec
		} else {
			vec[x - 1] < v // insert at end of vec
		}
	}
)]
fn binary_search<T : Ord>(vec: &Vec<T>, v : &T) -> Result<usize, usize> {
  Ok(0)
}

fn main () {}
