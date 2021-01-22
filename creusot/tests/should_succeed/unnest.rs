 #![feature(register_tool)]
#![register_tool(creusot)]
extern crate creusot_contracts;

use creusot_contracts::*;

fn main () {
}

#[ensures(* result == **x)]
#[ensures(^ result == *^x)]
#[ensures(^* x == ^ ^ x)]
fn unnest<'a, 'b : 'a>(x : &'a mut &'b mut u32) -> &'a mut u32 {
  * x
}

struct MyInt(usize);

// Is it possible to construct this argument?
// If each time a borrow is created we require borrowed place to outlive the borrow...
// Why not error though?
// fn unnest2<'b, 'a, MyInt >(x : &'a &'b MyInt) -> &'a MyInt {
//   &** x
// }
