extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[ensures(match result {
    Some(true) => true,
    _ => false,
})]
pub fn h() -> Option<bool> {
    Some(true)
}
