extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(true)]
fn omg(x: &[bool]) -> impl Iterator<Item = bool> {
    x.into_iter()
}
