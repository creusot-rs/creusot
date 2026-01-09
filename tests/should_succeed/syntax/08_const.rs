extern crate creusot_std;
use creusot_std::{logic::Seq, prelude::*};

#[logic(open)]
pub fn omg<T>() -> Seq<T> {
    Seq::empty()
}
