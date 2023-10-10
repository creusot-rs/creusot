#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

trait MyTrait<'x> {
    fn test(x: &'x mut u32);
}

struct MyStruct;

impl<'x> MyTrait<'x> for MyStruct {
    #[ensures(*x == 5u32)]
    fn test(x: &'x mut u32) {
        *x = 5;
    }
}
