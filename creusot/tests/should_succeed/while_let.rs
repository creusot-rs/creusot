#![feature(register_tool)]
#![register_tool(creusot)]

extern crate creusot_contracts;
use creusot_contracts::*;

enum Option<T> {
    Some(T),
    None,
}

use Option::*;

fn main() {
    let mut a = Some(10);
    let b = &mut a;

    invariant!(dummy, true);
    while let Some(_) = b {
        *b = None;
    }
}
