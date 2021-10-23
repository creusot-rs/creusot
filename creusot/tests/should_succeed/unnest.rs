extern crate creusot_contracts;

use creusot_contracts::*;

fn main() {}

#[ensures(*result == **x)]
#[ensures(^result == *^x)]
#[ensures(^*x == ^^x)]
fn unnest<'a, 'b: 'a>(x: &'a mut &'b mut u32) -> &'a mut u32 {
    *x
}
