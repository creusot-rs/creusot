extern crate creusot_contracts;
use creusot_contracts::*;

#[trusted]
#[logic]
#[ensures(true && false)]
#[creusot::builtins = "dummy_function"]
pub fn builtin_with_contract() {}
