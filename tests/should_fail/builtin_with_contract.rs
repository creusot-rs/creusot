extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[logic]
#[ensures(true && false)]
#[builtin("dummy_function")]
pub fn builtin_with_contract() {}
