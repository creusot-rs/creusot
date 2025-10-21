extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub struct Test;

impl Test {
    #[logic(open)]
    pub fn new() -> Test {
        Test
    }
}

#[logic(open)]
#[ensures(result == Test::new())]
pub fn test() -> Test {
    Test::new()
}
