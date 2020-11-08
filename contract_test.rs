#![feature(register_tool)]
#![register_tool(creusot)]
extern crate creusot_contracts;
use creusot_contracts::*;

// fn complex_contract(y: u32) {
//     match y {
//         0 => match y {
//              1 => true,
//              2 => false,
//             },
//         _ => false,
//         };
// }



// #[requires((1 + 1) ==> (1 + 1))]
// #[requires(if x == 0 { true } else { false })]
#[requires( true == > true ==> true)]
#[requires( true ==> true ==> false)]
fn my_func (x: u32) {

}



fn main () {}

#[ensures(   x <= 100 ==> result == 91
          && x > 100 ==> result == x - 10)]
fn mc91(x: u32) {

}
