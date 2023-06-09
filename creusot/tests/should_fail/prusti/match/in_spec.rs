extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(*(if b {x} else {result}) == 5u32)]
// this specification couldn't be translated to Creusot
// without pushing the de-reference through the if
fn lft_join4<'a, 'b: 'a>(x: &'a mut u32, y: &'b mut u32, b: bool) -> &'b mut u32 {
    *(if b {x} else {&mut *y}) = 5;
    y
}
