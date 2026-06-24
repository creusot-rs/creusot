extern crate creusot_std;
use creusot_std::prelude::*;

use std::iter::FromIterator;

#[ensures(result@ == x@)]
pub fn id<A>(x: Vec<A>) -> Vec<A> {
    Vec::from_iter(x.into_iter())
}
