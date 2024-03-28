extern crate creusot_contracts;

use creusot_contracts::{logic::Int, *};

fn test(mut x: (i32, (bool, u32))) {
    x.1.0 = true
}