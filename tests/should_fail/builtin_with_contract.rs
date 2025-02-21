extern crate creusot_contracts;
use creusot_contracts::*;

#[trusted]
#[logic]
#[ensures(true && false)]
#[creusot::builtins = "dummy_function"]
fn builtin_with_contract() {}
