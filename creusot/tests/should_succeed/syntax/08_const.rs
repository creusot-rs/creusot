extern crate creusot_contracts;
use creusot_contracts::{logic::Seq, *};

#[open]
#[ghost]
pub fn omg<T>() -> Seq<T> {
    Seq::EMPTY
}
