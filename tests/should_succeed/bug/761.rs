extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == x)]
pub fn try_option<T>(x: Option<T>) -> Option<T> {
    Some(x?)
}

#[ensures(result == x)]
pub fn try_result<T, E>(x: Result<T, E>) -> Result<T, E> {
    Ok(x?)
}

pub enum Empty {}

pub fn elim_empty(x: Empty) {
    match x {}
}
