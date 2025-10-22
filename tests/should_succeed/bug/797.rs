extern crate creusot_contracts;
use creusot_contracts::{logic::Mapping, prelude::*};

#[logic(open)]
pub fn make_mapping() -> Mapping<(Int, Int), bool> {
    |(x, y)| x + y == 0
}
