use creusot_contracts::prelude::*;

#[logic]
pub fn has_zero(v: (Int, Int, Int)) -> Int {
    pearlite! {
        match v {
            (0, _, _) | (_, 0, _) | (_, _, 0) => 1,
            _ => 0
        }
    }
}

