// WHY3PROVE
#![allow(unused)]

extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub fn f<const N: u32>(x: u32, y: u32) {
    const { N + 1 };
}
