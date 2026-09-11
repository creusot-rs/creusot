extern crate creusot_std;
use creusot_std::prelude::*;

#[logic_alias(
    let boxed = Box::new(2);
    let leaked = Box::leak(boxed);
    x + *leaked
)]
pub fn foo(x: i64) -> i64 {
    x + 2
}
