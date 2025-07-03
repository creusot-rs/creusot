extern crate creusot_contracts;
use creusot_contracts::{logic::Seq, *};

#[open]
#[logic]
pub fn omg<T>() -> Seq<T> {
    Seq::empty()
}
