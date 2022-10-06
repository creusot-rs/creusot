extern crate creusot_contracts;
use creusot_contracts::{logic::Seq, *};

#[logic]
pub fn omg<T>() -> Seq<T> {
    Seq::EMPTY
}
