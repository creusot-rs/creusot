extern crate creusot_std;

use creusot_std::prelude::*;

pub trait T {
    fn default(&self) -> u32 {
        0
    }

    #[logic(open)]
    fn logic_default(self) -> bool {
        true
    }
}

impl T for u32 {}

#[ensures(x.logic_default())]
pub fn should_use_impl(x: u32) {
    x.default();
}
