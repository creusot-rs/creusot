extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(*result == **x)]
#[ensures(^result == *^x)]
#[ensures(^*x == ^^x)]
pub fn unnest<'a, 'b: 'a>(x: &'a mut &'b mut u32) -> &'a mut u32 {
    *x
}
