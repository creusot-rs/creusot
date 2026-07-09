extern crate creusot_std;
use creusot_std::prelude::*;

// `#[check(terminates)]` functions allow recursive calls,
// which we must distinguish from this kind of recursion.
#[check(terminates)]
#[ensures(!f.postcondition((), ()))]
#[variant(())]
pub fn f() {}
