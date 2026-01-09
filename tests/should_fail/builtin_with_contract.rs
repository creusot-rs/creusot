extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(true && false)]
#[builtin("dummy_function")]
pub fn builtin_with_contract() {}
