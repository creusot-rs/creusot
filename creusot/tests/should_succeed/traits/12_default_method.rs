extern crate creusot_contracts;

use creusot_contracts::*;

trait T {
    fn default(&self) -> u32 {
        0
    }

    #[logic]
    fn logic_default(self) -> bool {
        true
    }
}

impl T for u32 {}

#[ensures(x.logic_default())]
fn should_use_impl(x: u32) {
    x.default();
}
