#![allow(unused)]

extern crate creusot_std;

use creusot_std::prelude::*;


#[requires(x@ < i64::MAX@ - 2)]
#[logic_alias(x + 1i64)]
const fn add_one(x: i64) -> i64 {
    x + 1
}



#[requires(a@ < i64::MAX@ - 3)]
#[ensures(result == add_one(add_one(a)))]
fn add_two(a: i64) -> i64 {
    a + 2
}
