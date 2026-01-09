extern crate creusot_std;
use creusot_std::{logic::Mapping, prelude::*};

#[logic(open)]
pub fn make_mapping() -> Mapping<(Int, Int), bool> {
    |(x, y)| x + y == 0
}
