// SHOULD_SUCCEED: parse-print
#![feature(register_tool)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;


fn test () {
		let mut x = 3;
		let y = &mut x;
		let mut z = &mut 6;
		* y = 4;
		z = &mut *y;
		* z = 5;

}

enum Option<T> {
    None,
    Some(T),
}

use Option::*;

pub struct List(u32,Option<Box<List>>);


#[logic]
// #[variant(len(l))]
fn get_opt(l : List, ix : Int) -> Option<u32> {{
    let List(i, ls) = l;
    match (ix > 0) {
        false => Some(i),
        true => match ls {
            Some(ls) => get_opt(ls, ix - 1),
            None => None
        }
    }
}}

// #[logic]
// fn logic_test() -> Option<u32> {{
//    (logic_test() == None) ; None
// }}


fn test2 () {
  let mut x = 3;
  let mut y = 6;

  let z = &mut x;
  let mut a = &mut y;

  * z = 5;
  * a = 3;
  a = &mut *z;

  * a = 8;
}

fn test3 () {
  let mut x = (5, 6);

  let a = &mut x;

  let b = &mut a.1;

  * b = 10;

  // assert * a = (5, 10)

  a.1 = 15;

  // assert x = (5, 15)
}

fn main () {}
