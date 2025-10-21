extern crate creusot_contracts;
use creusot_contracts::{logic::Seq, prelude::*};

#[logic(open)]
pub fn omg<T>() -> Seq<T> {
    Seq::empty()
}
