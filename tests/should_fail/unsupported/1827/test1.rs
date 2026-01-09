// ISSUE 1827: Pattern matching on Int is unsupported by Pearlite

use creusot_std::prelude::*;

#[logic]
#[variant(arr.len())]
fn sum(arr: Seq<Int>) -> Int {
    pearlite! {
        match arr.len() {
            0 => 0,
            _ => arr[0] + sum(arr.pop_front()),
        }
    }
}
