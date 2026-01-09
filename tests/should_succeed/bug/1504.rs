extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(match result {
    Some(true) => true,
    _ => false,
})]
pub fn h() -> Option<bool> {
    Some(true)
}
